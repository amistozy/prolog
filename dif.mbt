///|
/// `dif(X, Y)`: a disequality constraint, modeled after Scryer Prolog's
/// `library(dif)` (`reference/scryer-prolog/src/lib/dif.pl`).
///
/// `dif(X, Y)` succeeds when `X` and `Y` can be shown to be different, and
/// fails when they are already identical. When the two terms are not yet
/// comparable (e.g. `dif(X, b)` with `X` unbound), the constraint is
/// recorded in the machine and re-checked after every later binding, so a
/// later `X = b` fails. Constraints are undone on backtracking like choice
/// points.
///
/// Unlike `\=/2` (ISO "not unifiable", which fails as soon as the terms
/// could unify), `dif/2` delays the decision, which makes it fully
/// relational:
///
/// ```mbt check
/// test {
///   let p = Program([])
///   let x = variable("X")
///   // dif(X, b) succeeds with a pending constraint ...
///   let a1 = p.solve([x.dif(atom("b"))]).to_array()
///   assert_eq(a1.length(), 1)
///   // ... and X = b is rejected afterwards
///   let a2 = p.solve([x.dif(atom("b")), x.eq(atom("b"))]).to_array()
///   assert_eq(a2.length(), 0)
///   // X = a is fine
///   let a3 = p.solve([x.dif(atom("b")), x.eq(atom("a"))]).to_array()
///   assert_eq(a3.length(), 1)
///   // ground terms decide immediately
///   assert_eq(p.solve([atom("a").dif(atom("b"))]).to_array().length(), 1)
///   assert_eq(p.solve([atom("a").dif(atom("a"))]).to_array().length(), 0)
/// }
/// ```
fn Machine::dif(self : Machine, a : Term, b : Term) -> Bool {
  let da = a.deref(self.subst)
  let db = b.deref(self.subst)
  if identical_terms(da, db) {
    return false
  }
  if da.unify(db, self.subst) is None {
    // Provably different now; unification is monotone, so they can never
    // become identical later.
    return true
  }
  self.diffs.push((a, b))
  true
}
