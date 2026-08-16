///|
/// Dynamic predicates: `asserta/1`, `assertz/1`, `retract/1`,
/// `retractall/1`, `abolish/1`, `clause/2` and `dynamic/1`, modeled after
/// Scryer Prolog's dynamic clause store (`src/machine/loader.rs`).
///
/// The store lives inside [`Program`] in a `Ref`, so every machine created
/// from the same program shares it: assertions persist across queries on
/// the same `Program` value, exactly like a Prolog database.
///
/// Semantics notes:
///
/// - `assertz/1` appends and `asserta/1` inserts at the front; asserting a
///   *new* predicate makes it dynamic (like Scryer), asserting onto an
///   existing *static* predicate fails (Scryer raises a permission error;
///   this EDSL reports it as failure).
/// - `retract/1` marks the first matching clause dead; backtracking
///   retracts the next match. A retracted clause is never used again, even
///   by choice points created before the retraction, and retraction is not
///   undone on backtracking (like Scryer). Clauses are never physically
///   removed, so pending choice-point indexes stay valid.
/// - `clause/2` enumerates the clauses of a dynamic predicate with fresh
///   variables; it fails on static predicates.
/// - `:- dynamic(...)` directives are honored by [`parse_program`].

///|
/// The dynamic clause list of one predicate. Clauses are never removed;
/// `retract`/`retractall` mark them dead, so the index of a pending choice
/// point never shifts (only `asserta` inserts, at position 0, which skips
/// the new clause for already-created choice points — the SWI behavior).
///
/// Public only because [`Program`] references it; the fields are private
/// and there is no public constructor, so users cannot build or inspect
/// one.
pub(all) struct DynPred {
  mut next_id : Int
  clauses : Array[DynClause]
} derive(Debug)

///|
/// One stored dynamic clause: a unique id within its predicate plus the
/// `dead` flag set by retraction. Public only because [`DynPred`]
/// references it.
pub(all) struct DynClause {
  id : Int
  mut dead : Bool
  clause : Clause
} derive(Debug)

///|
/// Is `key` a dynamic predicate of the program?
fn Program::is_dynamic(self : Program, key : (String, Int)) -> Bool {
  self.dyn_store.val.contains(key)
}

///|
/// The dynamic clause list of `key`, creating it (and thereby declaring
/// `key` dynamic) when missing.
fn Program::dyn_pred(self : Program, key : (String, Int)) -> Ref[DynPred] {
  match self.dyn_store.val.get(key) {
    Some(pred) => pred
    None => {
      let pred = Ref({ next_id: 0, clauses: [] })
      self.dyn_store.val[key] = pred
      pred
    }
  }
}

///|
/// Declares `key` a dynamic predicate. Static clauses of `key` (if any)
/// are moved into the dynamic store, preserving their order, so a predicate
/// is always either static or dynamic, never both.
///
/// ```mbt check
/// test {
///   let p = Program([Clause::fact(compound("s", [atom("a")]))])
///   p.declare_dynamic(("s", 1))
///   // the static clause is now retractable
///   let answers = p
///     .solve([compound("retract", [compound("s", [atom("a")])])])
///     .to_array()
///   assert_eq(answers.length(), 1)
/// }
/// ```
pub fn Program::declare_dynamic(self : Program, key : (String, Int)) -> Unit {
  match self.clauses.get(key) {
    Some(cls) => {
      let pred = self.dyn_pred(key)
      for c in cls {
        pred.val.clauses.push({ id: pred.val.next_id, dead: false, clause: c })
        pred.val.next_id = pred.val.next_id + 1
      }
      self.clauses.remove(key)
    }
    None => {
      let _ = self.dyn_pred(key)
    }
  }
}

///|
/// The clauses of `key` to try when calling it: the live dynamic clauses
/// for a dynamic predicate, the static clauses otherwise.
fn Machine::clauses_of(self : Machine, key : (String, Int)) -> Array[Clause]? {
  match self.prog.dyn_store.val.get(key) {
    Some(pred) => {
      let live : Array[Clause] = []
      for dc in pred.val.clauses {
        if !dc.dead {
          live.push(dc.clause)
        }
      }
      Some(live)
    }
    None => self.prog.clauses.get(key)
  }
}

///|
/// `asserta(Clause)` / `assertz(Clause)`: inserts a rule or fact into the
/// dynamic store, at the front or the end respectively. The clause is
/// copied: bound variables become their values, free variables are renamed
/// to fresh ones (like `findall/3`), so the asserted clause never shares
/// variables with the query.
fn Machine::assert_goal(self : Machine, t : Term, prepend : Bool) -> Bool {
  let resolved = fresh_vars(t.resolve(self.subst))
  let (head, body) = match resolved {
    Compound(":-", [h, b]) => (h, b)
    _ => (resolved, Atom("true"))
  }
  match head.head_key() {
    None => false
    Some(key) => {
      if self.prog.clauses.contains(key) && !self.prog.is_dynamic(key) {
        // permission error: static predicate (cf. Scryer) — reported as
        // failure in this EDSL.
        return false
      }
      let pred = self.prog.dyn_pred(key)
      let dc = { id: pred.val.next_id, dead: false, clause: Clause(head, body) }
      if prepend {
        pred.val.clauses.insert(0, dc)
      } else {
        pred.val.clauses.push(dc)
      }
      pred.val.next_id = pred.val.next_id + 1
      true
    }
  }
}

///|
/// `retract(Clause)`: marks the first non-dead clause that unifies with
/// `Clause` as dead. Backtracking retracts the next matching clause (via
/// the private `$retract_next` cursor goal); like Scryer, retraction is
/// permanent — it is not undone on backtracking.
fn Machine::retract(self : Machine, h : Term, mark : Int) -> Bool {
  match h.deref(self.subst) {
    Compound(":-", [head, body]) => self.retract_from(head, body, 0, mark)
    t => self.retract_from(t, Atom("true"), 0, mark)
  }
}

///|
/// The private goal that resumes a `retract/1` search after a choice point:
/// `$retract_next(Name, Arity, Head, Body, From)`.
fn retract_next_goal(
  key : (String, Int),
  head : Term,
  body : Term,
  from : Int,
) -> Term {
  compound("$retract_next", [atom(key.0), int(key.1), head, body, int(from)])
}

///|
fn Machine::retract_from(
  self : Machine,
  head : Term,
  body : Term,
  from : Int,
  mark : Int,
) -> Bool {
  match head.head_key() {
    None => false
    Some(key) => self.retract_from_key(key, head, body, from, mark)
  }
}

///|
fn Machine::retract_from_key(
  self : Machine,
  key : (String, Int),
  head : Term,
  body : Term,
  from : Int,
  mark : Int,
) -> Bool {
  match self.prog.dyn_store.val.get(key) {
    None => false
    Some(pred) =>
      match self.find_retract_index(pred.val, head, body, from) {
        None => false
        Some((i, s2)) => {
          if i + 1 < pred.val.clauses.length() {
            self.push_choice(
              Goal(goal=retract_next_goal(key, head, body, i + 1), mark~),
            )
          }
          pred.val.clauses[i].dead = true
          // the head/body unification is committed, so e.g.
          // `retract(r(Y))` binds the caller's `Y`
          self.commit(s2)
        }
      }
  }
}

///|
/// The first non-dead clause of `pred`, at index `>= from`, whose head and
/// body unify with `head` / `body` (clauses are standardized apart first,
/// like in `clause/2`), together with the unifying substitution.
fn Machine::find_retract_index(
  self : Machine,
  pred : DynPred,
  head : Term,
  body : Term,
  from : Int,
) -> (Int, Subst)? {
  for i in from..<pred.clauses.length() {
    let dc = pred.clauses[i]
    if dc.dead {
      continue
    }
    let (rh, rb) = fresh_rename(dc.clause)
    match head.unify(rh, self.subst) {
      None => continue
      Some(s2) => if body.unify(rb, s2) is Some(s3) { return Some((i, s3)) }
    }
  }
  None
}

///|
/// Executes a `$retract_next(Name, Arity, Head, Body, From)` goal.
fn Machine::retract_next(
  self : Machine,
  args : Array[Term],
  mark : Int,
) -> Bool {
  guard args is [kname, karity, head, body, from] else { return false }
  match
    (kname.deref(self.subst), karity.deref(self.subst), from.deref(self.subst)) {
    (Atom(name), Int(arity), Int(from_i)) if from_i >= 0 =>
      self.retract_from_key((name, arity), head, body, from_i, mark)
    _ => false
  }
}

///|
/// `retractall(Head)`: marks every non-dead clause whose head unifies with
/// `Head` as dead. Always succeeds, like the ISO predicate.
fn Machine::retractall(self : Machine, h : Term) -> Unit {
  let head = h.deref(self.subst)
  match head.head_key() {
    None => ()
    Some(key) =>
      match self.prog.dyn_store.val.get(key) {
        None => ()
        Some(pred) =>
          for i in 0..<pred.val.clauses.length() {
            let dc = pred.val.clauses[i]
            if dc.dead {
              continue
            }
            let (rh, _) = fresh_rename(dc.clause)
            if head.unify(rh, self.subst) is Some(_) {
              pred.val.clauses[i].dead = true
            }
          }
      }
  }
}

///|
/// `clause(Head, Body)`: unifies `Head` and `Body` with a fresh copy of
/// each clause of a dynamic predicate, enumerating them on backtracking.
/// With a variable `Head`, every dynamic predicate is searched. Fails on
/// static predicates (Scryer raises a permission error).
fn Machine::clause_goal(self : Machine, h : Term, b : Term, mark : Int) -> Bool {
  // (key, fresh head, fresh body) for every live dynamic clause; a
  // variable head searches the whole store, a callable head only its key.
  let matches : Array[((String, Int), Term, Term)] = []
  let head = h.deref(self.subst)
  let keys : Array[(String, Int)] = match head.head_key() {
    Some(key) => [key]
    None =>
      if head is Var(_) {
        self.prog.dyn_store.val.keys().to_array()
      } else {
        return false
      }
  }
  for key in keys {
    match self.prog.dyn_store.val.get(key) {
      None => continue
      Some(pred) =>
        for dc in pred.val.clauses {
          if dc.dead {
            continue
          }
          let (rh, rb) = fresh_rename(dc.clause)
          matches.push((key, rh, rb))
        }
    }
  }
  if matches.length() == 0 {
    return false
  }
  for i = matches.length() - 1; i >= 1; i = i - 1 {
    let (_, rh, rb) = matches[i]
    self.push_choice(Goal(goal=h.eq(rh) & b.eq(rb), mark~))
  }
  let (_, rh, rb) = matches[0]
  self.unify_goal(h, rh) && self.unify_goal(b, rb)
}

///|
/// `abolish(Name/Arity)`: removes a dynamic predicate entirely. Fails on
/// static predicates and non-indicator arguments.
fn Machine::abolish(self : Machine, i : Term) -> Bool {
  match i.deref(self.subst) {
    Compound("/", [Atom(name), Int(arity)]) if arity >= 0 =>
      if self.prog.clauses.contains((name, arity)) {
        false
      } else {
        let _ = self.prog.dyn_store.val.remove((name, arity))
        true
      }
    _ => false
  }
}

///|
/// `dynamic(Spec)`: declares a predicate dynamic at runtime. `Spec` is a
/// predicate indicator (`p/1`) or a callable term (`p`, `p(X)`).
fn Machine::dynamic(self : Machine, spec : Term) -> Bool {
  match spec.deref(self.subst) {
    Compound("/", [Atom(name), Int(arity)]) if arity >= 0 => {
      self.prog.declare_dynamic((name, arity))
      true
    }
    t =>
      match t.head_key() {
        Some(key) => {
          self.prog.declare_dynamic(key)
          true
        }
        None => false
      }
  }
}
