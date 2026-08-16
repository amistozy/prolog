///|
/// A goal frame on the goal stack: the goal plus the cut mark of the clause
/// body it belongs to. The mark is the length of the choice-point stack when
/// the enclosing clause was entered; `!` truncates the stack to it.
priv struct Frame {
  goal : Term
  mark : Int
} derive(Debug)

///|
/// Immutable goal stack. Pushing creates a new cell, so frames pushed before
/// a choice point are automatically snapshotted by reference.
priv enum FStack {
  FNil
  FCons(Frame, FStack)
} derive(Debug)

///|
/// How to resume from a choice point during backtracking.
priv enum Alt {
  /// Try the next clause of a predicate call.
  Clauses(goal~ : Term, key~ : (String, Int), next~ : Int)
  /// Solve a pending goal, e.g. the second branch of a disjunction.
  Goal(goal~ : Term, mark~ : Int)
}

///|
/// A suspended search state that backtracking can resume.
priv struct Choice {
  goals : FStack
  subst : Subst
  /// Number of active `dif/2` constraints when the choice point was pushed;
  /// backtracking truncates `Machine.diffs` back to this length.
  diffs_len : Int
  alt : Alt
}

///|
/// The SLD resolution machine. `subst` maps are never mutated in place, so
/// each choice point holds an implicit snapshot of the substitution.
///
/// `diffs` holds the active `dif/2` disequality constraints; like `choices`,
/// it is truncated on backtracking (see [`Choice::diffs_len`]).
priv struct Machine {
  prog : Program
  mut stack : FStack
  mut subst : Subst
  choices : Array[Choice]
  /// Active `dif/2` constraints, in the order they were posted.
  diffs : Array[(Term, Term)]
  /// True right after a solution has been yielded; the next step must
  /// resume by backtracking.
  mut resumed : Bool
}

///|
/// Builds a fresh machine for the given program, with an empty goal stack,
/// substitution, constraint store and no choice points.
///
/// Declared as the custom constructor `Machine(...)`, like
/// [`Clause::Clause`](index.html#clause).
fn Machine::Machine(prog : Program) -> Machine {
  {
    prog,
    stack: FNil,
    subst: @immut_hashmap.HashMap([]),
    choices: [],
    diffs: [],
    resumed: false,
  }
}

///|
/// Records a choice point, snapshotting the current goal stack, substitution
/// and `dif/2` constraint count.
fn Machine::push_choice(self : Machine, alt : Alt) -> Unit {
  self.choices.push({
    goals: self.stack,
    subst: self.subst,
    diffs_len: self.diffs.length(),
    alt,
  })
}

///|
/// Commits `s` as the machine's substitution. Returns `false` when `s`
/// violates an active `dif/2` constraint (the caller must then fail and
/// backtrack).
fn Machine::commit(self : Machine, s : Subst) -> Bool {
  self.subst = s
  self.check_diffs(s)
}

///|
/// Checks every active `dif/2` constraint against substitution `s`: if any
/// two constrained terms have become identical, the constraint is violated.
/// Permanently-satisfied constraints are kept (they never fail again), so
/// this is a pure predicate over `s`.
fn Machine::check_diffs(self : Machine, s : Subst) -> Bool {
  for p in self.diffs {
    let (a, b) = p
    if identical_terms(a.deref(s), b.deref(s)) {
      return false
    }
  }
  true
}

///|
/// Pushes a goal frame with the given cut mark.
fn Machine::push_goal(self : Machine, g : Term, mark : Int) -> Unit {
  self.stack = FCons({ goal: g, mark }, self.stack)
}

///|
/// Runs the machine until it yields a solution or the search is exhausted.
///
/// - `goal_barrier`: the stack reference that counts as "no goals left"
///   (the top-level solver uses `FNil`; `not/1` uses the stack at its entry)
/// - `choice_barrier`: backtracking never pops choices below this index
///   (`-1` means no barrier; `not/1` uses the choice count at its entry)
fn Machine::step(
  self : Machine,
  goal_barrier : FStack,
  choice_barrier : Int,
) -> Subst? {
  for ;; {
    if self.resumed {
      self.resumed = false
      if !self.backtrack(choice_barrier) {
        return None
      }
    }
    // Solve goals until failure, success, or exhaustion.
    for ;; {
      match self.stack {
        _ if physical_equal(self.stack, goal_barrier) => {
          self.resumed = true
          return Some(self.subst)
        }
        FNil => abort("internal error: goal stack underflow")
        FCons(fr, rest) => {
          self.stack = rest
          if !self.execute(fr) {
            break
          }
        }
      }
    }
    // The current branch failed; backtrack and try the next alternative.
    if !self.backtrack(choice_barrier) {
      return None
    }
  }
}

///|
/// Pops choice points and tries their alternatives until one succeeds or the
/// search space is exhausted (respecting `choice_barrier`).
fn Machine::backtrack(self : Machine, choice_barrier : Int) -> Bool {
  for ;; {
    if self.choices.length() == choice_barrier {
      return false
    }
    match self.choices.pop() {
      None => return false
      Some(ch) => {
        self.stack = ch.goals
        self.subst = ch.subst
        self.diffs.truncate(ch.diffs_len)
        match ch.alt {
          Clauses(goal=g, key=k, next=n) => {
            let mark = self.choices.length()
            match self.prog.clauses.get(k) {
              None => continue
              Some(cls) =>
                if self.try_clauses(g, k, cls, n, mark) {
                  return true
                }
            }
          }
          Goal(goal=g, mark=m) => {
            self.push_goal(g, m)
            return true
          }
        }
      }
    }
  }
}

///|
/// Executes one goal frame. Returns `false` when the goal fails, which makes
/// the caller backtrack.
fn Machine::execute(self : Machine, fr : Frame) -> Bool {
  let g = fr.goal.deref(self.subst)
  match g {
    Atom(name) =>
      match name {
        "true" => true
        "fail" | "false" => false
        "!" => {
          self.choices.truncate(fr.mark)
          true
        }
        _ => self.call_pred(g, (name, 0))
      }
    Compound(name, args) =>
      if name == "," && args.length() == 2 {
        self.push_goal(args[1], fr.mark)
        self.push_goal(args[0], fr.mark)
        true
      } else if name == ";" && args.length() == 2 {
        match args[0] {
          // (A -> B ; C): soft cut — commit to B once A succeeds.
          Compound("->", [cond, then]) => {
            let m0 = self.choices.length()
            self.push_choice(Goal(goal=args[1], mark=fr.mark))
            // Execute order (LIFO): cond, then `!`, then the committed
            // branch.
            self.push_goal(then, fr.mark)
            self.push_goal(atom("!"), m0)
            self.push_goal(cond, fr.mark)
            true
          }
          _ => {
            self.push_choice(Goal(goal=args[1], mark=fr.mark))
            self.push_goal(args[0], fr.mark)
            true
          }
        }
      } else if name == "->" && args.length() == 2 {
        // (A -> B) without an else branch: commit to B once A succeeds,
        // and fail entirely when A fails.
        let m0 = self.choices.length()
        self.push_goal(args[1], fr.mark)
        self.push_goal(atom("!"), m0)
        self.push_goal(args[0], fr.mark)
        true
      } else {
        match self.run_builtin(name, args, fr.mark) {
          Some(result) => result
          None => self.call_pred(g, (name, args.length()))
        }
      }
    _ => false
  }
}

///|
/// Calls a user predicate: tries its clauses in order, standardizing apart
/// (renaming the clause's variables) before each attempt.
fn Machine::call_pred(self : Machine, g : Term, key : (String, Int)) -> Bool {
  let mark = self.choices.length()
  match self.prog.clauses.get(key) {
    None => false
    Some(cls) => self.try_clauses(g, key, cls, 0, mark)
  }
}

///|
/// Tries clauses `cls[idx..]` against goal `g`. `mark` is the choice length
/// recorded when the call was made (used by cut).
fn Machine::try_clauses(
  self : Machine,
  g : Term,
  key : (String, Int),
  cls : Array[Clause],
  idx : Int,
  mark : Int,
) -> Bool {
  for i in idx..<cls.length() {
    let cl = cls[i]
    let (head, body) = fresh_rename(cl)
    match g.unify(head, self.subst) {
      None => continue
      Some(s2) =>
        // Reject the clause when the binding violates a `dif/2` constraint.
        if self.check_diffs(s2) {
          if i + 1 < cls.length() {
            self.push_choice(Clauses(goal=g, key~, next=i + 1))
          }
          self.subst = s2
          if !(body is Atom("true")) {
            self.push_goal(body, mark)
          }
          return true
        }
    }
  }
  false
}

///|
/// Standardizes a clause apart: renames every variable of head and body to a
/// fresh id, so repeated invocations of the same clause share no variables.
fn fresh_rename(cl : Clause) -> (Term, Term) {
  let ids = collect_var_ids(cl.head, collect_var_ids(cl.body, Map([])))
  let map : Map[Int, Int] = Map([])
  for id, _ in ids {
    map[id] = fresh_id()
  }
  (rename_vars(cl.head, map), rename_vars(cl.body, map))
}

///|
/// Allocates a fresh variable id from the global counter.
fn fresh_id() -> Int {
  var_counter.val = var_counter.val + 1
  var_counter.val
}

///|
/// `not(g)`: succeeds iff `g` has no solution. `g` runs with a fresh cut
/// mark and fresh barriers, so cuts inside `g` cannot escape its scope.
fn Machine::not(self : Machine, g : Term) -> Bool {
  let saved_stack = self.stack
  let saved_subst = self.subst
  let choice_barrier = self.choices.length()
  let diff_barrier = self.diffs.length()
  self.push_goal(g, choice_barrier)
  let succeeded = self.step(saved_stack, choice_barrier) is Some(_)
  self.stack = saved_stack
  self.subst = saved_subst
  self.choices.truncate(choice_barrier)
  self.diffs.truncate(diff_barrier)
  self.resumed = false
  !succeeded
}

///|
/// All solutions of the query (a conjunction of goals) as a lazy iterator of
/// raw substitutions.
pub fn Program::solve_subst(self : Program, goals : Array[Term]) -> Iter[Subst] {
  let m = Machine(self)
  // Push in reverse: the goal stack pops the last pushed frame first, so
  // goals are executed in their given order.
  for i = goals.length() - 1; i >= 0; i = i - 1 {
    m.push_goal(goals[i], 0)
  }
  Iter::new(() => m.step(FNil, -1))
}

///|
/// One answer of a query: the bindings of the query's variables, keyed by
/// name (anonymous variables starting with `_` are skipped).
///
/// `order` records the names in order of first appearance in the query, so
/// answers render deterministically as `X = john, Y = mary` regardless of
/// hash-map iteration order.
struct Answer {
  bindings : Map[String, Term]
  order : Array[String]
} derive(Debug)

///|
/// Collects the named variables of the query, in order of first appearance.
fn collect_query_vars(goals : Array[Term]) -> Array[VarRef] {
  let seen : Map[Int, Unit] = Map([])
  let out : Array[VarRef] = []
  for g in goals {
    collect_vars_into(g, seen, out)
  }
  out
}

///|
fn collect_vars_into(
  t : Term,
  seen : Map[Int, Unit],
  out : Array[VarRef],
) -> Unit {
  match t {
    Var(v) =>
      if !seen.contains(v.id) {
        seen[v.id] = ()
        out.push(v)
      }
    List(xs) =>
      for x in xs {
        collect_vars_into(x, seen, out)
      }
    Compound(_, args) =>
      for x in args {
        collect_vars_into(x, seen, out)
      }
    _ => ()
  }
}

///|
/// Builds an [`Answer`] from a substitution and the query it answers.
/// Bindings that just say `X = X` (an unbound query variable) are omitted.
pub fn Answer::from_subst(subst : Subst, goals : Array[Term]) -> Answer {
  let bindings : Map[String, Term] = Map([])
  let order : Array[String] = []
  for v in collect_query_vars(goals) {
    if v.name != "" && !v.name.has_prefix("_") && !bindings.contains(v.name) {
      let value = Var(v).resolve(subst)
      match value {
        Var(v2) =>
          if v2.id != v.id {
            bindings[v.name] = value
            order.push(v.name)
          }
        _ => {
          bindings[v.name] = value
          order.push(v.name)
        }
      }
    }
  }
  { bindings, order }
}

///|
/// The binding of the query variable named `name`, if any.
///
/// ```mbt check
/// test {
///   let x = variable("X")
///   let p = Program([Clause::fact(compound("p", [atom("a")]))])
///   let a = p.solve_first([compound("p", [x])]).unwrap()
///   assert_eq(a.get("X"), Some(atom("a")))
///   assert_eq(a.get("Y"), None)
/// }
/// ```
pub fn Answer::get(self : Answer, name : String) -> Term? {
  self.bindings.get(name)
}

///|
/// Renders an answer as `X = john, Y = mary` (or `true` for no bindings).
/// Bindings are listed in order of first appearance in the query.
pub impl Show for Answer with fn to_string(self) {
  let parts = self.order.map(name => "\{name} = \{self.bindings[name]}")
  if parts.length() == 0 {
    "true"
  } else {
    parts.join(", ")
  }
}

///|
/// Runs a query against the program, yielding each solution as an
/// [`Answer`]. The iterator is lazy: solutions are produced on demand, and
/// infinite solution spaces can be explored with `take`/`next`.
///
/// ```mbt check
/// test {
///   let p = Program([
///     Clause::fact(compound("parent", [atom("john"), atom("mary")])),
///     Clause::fact(compound("parent", [atom("john"), atom("jane")])),
///   ])
///   let x = variable("X")
///   let answers = p.solve([compound("parent", [x, variable("_")])]).to_array()
///   assert_eq(answers.length(), 2)
///   assert_eq(answers[0].to_string(), "X = john")
/// }
/// ```
pub fn Program::solve(self : Program, goals : Array[Term]) -> Iter[Answer] {
  self.solve_subst(goals).map(s => Answer::from_subst(s, goals))
}

///|
/// The first solution of a query, if any.
pub fn Program::solve_first(self : Program, goals : Array[Term]) -> Answer? {
  self.solve(goals).next()
}

///|
/// All solutions of a query. Use with care on programs with infinite
/// solution spaces (use [`solve`] with `take`/`next` instead).
pub fn Program::solve_all(self : Program, goals : Array[Term]) -> Array[Answer] {
  self.solve(goals).to_array()
}
