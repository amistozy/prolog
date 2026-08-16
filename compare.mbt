///|
/// Prolog standard order of terms (ISO 7.2, cf. Scryer's
/// `TermOrderCategory`): Variable < Float < Integer < Atom < Str < Compound.
///
/// Lists compare as cons chains (functor `"."`), like in ISO.
/// Both arguments should already be resolved (dereferenced) — builtins
/// resolve before comparing.

///|
/// [`Compare`](https://docs.moonbitlang.com/core/builtin/#Compare) for
/// terms: compares two resolved terms, returning a negative / zero /
/// positive int (like `compare/3`). Unbound variables compare by their id.
///
/// ```mbt check
/// test {
///   assert_true(atom("a").compare(int(1)) > 0)
///   assert_eq(int(1).compare(int(1)), 0)
///   // standard order: floats sort before integers, so Int(1) > Float(1.0)
///   assert_true(int(1).compare(float(1.0)) > 0)
/// }
/// ```
pub impl Compare for Term with fn compare(a : Term, b : Term) -> Int {
  match (a, b) {
    (Var(x), Var(y)) =>
      if x.id == y.id {
        0
      } else if x.id < y.id {
        -1
      } else {
        1
      }
    (Var(_), _) => -1
    (_, Var(_)) => 1
    (Float(x), Float(y)) => if x == y { 0 } else if x < y { -1 } else { 1 }
    (Float(_), _) => -1
    (_, Float(_)) => 1
    (Int(x), Int(y)) => if x == y { 0 } else if x < y { -1 } else { 1 }
    (Int(_), _) => -1
    (_, Int(_)) => 1
    (Atom(x), Atom(y)) => compare_strings(x, y)
    (Atom(_), _) => -1
    (_, Atom(_)) => 1
    (Str(x), Str(y)) => compare_strings(x, y)
    (Str(_), _) => -1
    (_, Str(_)) => 1
    _ => compare_compounds(a, b)
  }
}

///|
/// Compound terms (and lists) compare by functor name, then arity, then
/// arguments, left to right.
fn compare_compounds(a : Term, b : Term) -> Int {
  // Lists are cons chains in ISO: functor "." with arity 2.
  let (fa, aa) = match a {
    List(_) => (".", 2)
    Compound(f, args) => (f, args.length())
    _ => abort("compare_compounds: not a compound")
  }
  let (fb, ab) = match b {
    List(_) => (".", 2)
    Compound(f, args) => (f, args.length())
    _ => abort("compare_compounds: not a compound")
  }
  let fc = compare_strings(fa, fb)
  if fc != 0 {
    fc
  } else if aa != ab {
    if aa < ab {
      -1
    } else {
      1
    }
  } else {
    compare_args(a, b)
  }
}

///|
fn compare_args(a : Term, b : Term) -> Int {
  let xs = match a {
    List(xs) => xs
    Compound(_, args) => args
    _ => abort("compare_args: not a compound")
  }
  let ys = match b {
    List(xs) => xs
    Compound(_, args) => args
    _ => abort("compare_args: not a compound")
  }
  let n = if xs.length() < ys.length() { xs.length() } else { ys.length() }
  for i in 0..<n {
    let c = xs[i].compare(ys[i])
    if c != 0 {
      return c
    }
  }
  0
}

///|
fn compare_strings(a : String, b : String) -> Int {
  if a == b {
    0
  } else if a < b {
    -1
  } else {
    1
  }
}
