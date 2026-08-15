///|
/// A substitution maps variable ids to terms.
///
/// Unification never mutates an existing map in place: every binding step
/// produces a *new* map, so a substitution value can be shared safely across
/// branches (this is what makes backtracking and `not/1` easy to implement).
pub type Subst = Map[Int, Term]

///|
/// Follows the binding chain of `self`, returning the current value of the
/// variable (or the term itself if it is not a bound variable).
///
/// ```mbt check
/// test {
///   let x = variable("X")
///   let y = variable("Y")
///   let s : Subst = Map([])
///   let s2 = match x.unify(y, s) {
///     Some(s2) => s2
///     None => abort("unify failed")
///   }
///   let s3 = match y.unify(atom("a"), s2) {
///     Some(s3) => s3
///     None => abort("unify failed")
///   }
///   assert_eq(x.deref(s3).to_string(), "a")
/// }
/// ```
pub fn Term::deref(self : Term, s : Subst) -> Term {
  let mut cur = self
  for ;; {
    match cur {
      Var(v) =>
        match s.get(v.id) {
          Some(bound) => cur = bound
          None => return cur
        }
      _ => return cur
    }
  }
}

///|
/// Fully resolves a term: bound variables are replaced by their values
/// recursively, unbound variables stay as they are.
pub fn Term::resolve(self : Term, s : Subst) -> Term {
  match self.deref(s) {
    Var(v) => Var(v)
    List(xs) => List(xs.map(x => x.resolve(s)))
    Compound(f, args) => Compound(f, args.map(x => x.resolve(s)))
    other => other
  }
}

///|
/// Robinson unification under substitution `s`. Returns `Some(s')` with the
/// new substitution when the two terms unify, `None` otherwise. The occur
/// check is performed, so cyclic bindings are rejected.
///
/// Numbers unify numerically: `Int(1)` and `Float(1.0)` unify.
/// Proper lists (built from `List`, `[]` or cons cells) unify regardless of
/// which representation each side uses.
///
/// ```mbt check
/// test {
///   let x = variable("X")
///   let s = x.unify(atom("a"), Map([]))
///   assert_true(s is Some(_))
/// }
/// ```
pub fn Term::unify(self : Term, other : Term, s : Subst) -> Subst? {
  let a = self.deref(s)
  let b = other.deref(s)
  match (a, b) {
    (Var(x), Var(y)) if x.id == y.id => Some(s)
    (Var(x), _) => bind(s, x.id, b)
    (_, Var(y)) => bind(s, y.id, a)
    _ => unify_ground(a, b, s)
  }
}

///|
/// Unification of two non-variable terms.
fn unify_ground(a : Term, b : Term, s : Subst) -> Subst? {
  match (list_parts(a), list_parts(b)) {
    (Some((ha, ta)), Some((hb, tb))) => {
      // Base cases for empty lists, so list unification always terminates.
      let a_empty = ha.length() == 0 && is_empty_list(ta)
      let b_empty = hb.length() == 0 && is_empty_list(tb)
      if a_empty && b_empty {
        return Some(s)
      }
      if a_empty || b_empty {
        return None
      }
      let n = if ha.length() < hb.length() { ha.length() } else { hb.length() }
      let mut cur : Subst? = Some(s)
      for i in 0..<n {
        match cur {
          None => break
          Some(si) => cur = ha[i].unify(hb[i], si)
        }
      }
      match cur {
        None => None
        Some(si) => unify_list_rest(ha, hb, n, ta, tb, si)
      }
    }
    _ =>
      match (a, b) {
        (Int(i), Int(j)) => if i == j { Some(s) } else { None }
        (Float(f), Float(g)) => if f == g { Some(s) } else { None }
        (Int(i), Float(f)) => if i.to_double() == f { Some(s) } else { None }
        (Float(f), Int(i)) => if f == i.to_double() { Some(s) } else { None }
        (Atom(x), Atom(y)) => if x == y { Some(s) } else { None }
        (Str(x), Str(y)) => if x == y { Some(s) } else { None }
        (Compound(f1, a1), Compound(f2, a2)) =>
          if f1 == f2 && a1.length() == a2.length() {
            let mut cur : Subst? = Some(s)
            for i in 0..<a1.length() {
              match cur {
                None => break
                Some(si) => cur = a1[i].unify(a2[i], si)
              }
            }
            cur
          } else {
            None
          }
        _ => None
      }
  }
}

///|
/// After unifying the common elements of two lists, unify what remains:
/// the tails `ta`/`tb`, plus any leftover elements of the longer side.
///
/// The remaining parts are unified recursively, which always consumes
/// structure; the empty-list base cases in [`unify_ground`] guarantee
/// termination.
fn unify_list_rest(
  ha : Array[Term],
  hb : Array[Term],
  n : Int,
  ta : Term,
  tb : Term,
  s : Subst,
) -> Subst? {
  if n < ha.length() && n < hb.length() {
    chain_from(ha, n, ta).unify(chain_from(hb, n, tb), s)
  } else if n < ha.length() {
    chain_from(ha, n, ta).unify(tb, s)
  } else if n < hb.length() {
    ta.unify(chain_from(hb, n, tb), s)
  } else {
    ta.unify(tb, s)
  }
}

///|
/// Is `t` an empty list (either representation)?
fn is_empty_list(t : Term) -> Bool {
  t is Atom("[]") || t is List([])
}

///|
/// Binds `id` to `t`, rejecting cyclic bindings via the occur check.
fn bind(s : Subst, id : Int, t : Term) -> Subst? {
  if occurs(id, t, s) {
    None
  } else {
    let s2 = s.copy()
    s2[id] = t
    Some(s2)
  }
}

///|
/// Occur check: does variable `id` occur inside `t` (after dereferencing)?
fn occurs(id : Int, t : Term, s : Subst) -> Bool {
  match t.deref(s) {
    Var(v) => v.id == id
    List(xs) => xs.any(x => occurs(id, x, s))
    Compound(_, args) => args.any(x => occurs(id, x, s))
    _ => false
  }
}

///|
/// Views a term as a list: `Some((elements, tail))` when `t` is a proper
/// list, a cons chain, or `[]`; `None` otherwise. The tail is `[]` for
/// proper lists and the residual term for partial lists.
fn list_parts(t : Term) -> (Array[Term], Term)? {
  let acc : Array[Term] = []
  let mut cur = t
  for ;; {
    match cur {
      Atom("[]") => return Some((acc, Atom("[]")))
      List(xs) => {
        for x in xs {
          acc.push(x)
        }
        return Some((acc, Atom("[]")))
      }
      Compound(".", [h, tail]) => {
        acc.push(h)
        cur = tail
      }
      _ =>
        // We left the chain: a non-empty accumulator means this is a
        // partial list `[h1, ..., hn | rest]`, and `rest` is the tail.
        if acc.length() > 0 {
          return Some((acc, cur))
        } else {
          return None
        }
    }
  }
}

///|
/// Rebuilds a cons chain from `elems[from..]` ending in `tail`.
fn chain_from(elems : Array[Term], from : Int, tail : Term) -> Term {
  let mut acc = tail
  for i = elems.length() - 1; i >= from; i = i - 1 {
    acc = Compound(".", [elems[i], acc])
  }
  acc
}

///|
/// Collects the ids of every variable occurring in `t` into `acc`.
fn collect_var_ids(t : Term, acc : Map[Int, Unit]) -> Map[Int, Unit] {
  match t {
    Var(v) => {
      acc[v.id] = ()
      acc
    }
    List(xs) => {
      for x in xs {
        let _ = collect_var_ids(x, acc)
      }
      acc
    }
    Compound(_, args) => {
      for x in args {
        let _ = collect_var_ids(x, acc)
      }
      acc
    }
    _ => acc
  }
}

///|
/// Renames the variables of `t` according to `map` (old id -> new id).
fn rename_vars(t : Term, map : Map[Int, Int]) -> Term {
  match t {
    Var(v) =>
      match map.get(v.id) {
        Some(new_id) => Var({ id: new_id, name: v.name })
        None => t
      }
    List(xs) => List(xs.map(x => rename_vars(x, map)))
    Compound(f, args) => Compound(f, args.map(x => rename_vars(x, map)))
    _ => t
  }
}
