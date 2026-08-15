///|
/// A small library of classic list / arithmetic predicates, implemented as
/// ordinary Prolog clauses so they stay fully relational (usable in any
/// argument direction):
///
/// - `member/2`, `append/3`, `length/2`, `reverse/2`, `between/3`
///
/// ```mbt check
/// test {
///   let p = stdlib()
///   let x = variable("X")
///   let answers = p
///     .solve([compound("member", [x, list([int(1), int(2), int(3)])])])
///     .to_array()
///   assert_eq(answers.length(), 3)
///   assert_eq(answers[0].to_string(), "X = 1")
///   assert_eq(answers[2].to_string(), "X = 3")
/// }
/// ```
pub fn stdlib() -> Program {
  let clauses : Array[Clause] = []
  for c in member_clauses() {
    clauses.push(c)
  }
  for c in append_clauses() {
    clauses.push(c)
  }
  for c in length_clauses() {
    clauses.push(c)
  }
  for c in reverse_clauses() {
    clauses.push(c)
  }
  for c in between_clauses() {
    clauses.push(c)
  }
  try! program(clauses)
}

///|
/// `member(X, [X | _]).` and `member(X, [_ | T]) :- member(X, T).`
fn member_clauses() -> Array[Clause] {
  let x = variable("X")
  let t = variable("T")
  let x2 = variable("X")
  let t2 = variable("T")
  [
    fact(compound("member", [x, cons(x, t)])),
    rule(
      compound("member", [x2, cons(variable("_"), t2)]),
      compound("member", [x2, t2]),
    ),
  ]
}

///|
/// `append([], L, L).` and `append([H | T], L, [H | R]) :- append(T, L, R).`
fn append_clauses() -> Array[Clause] {
  let l = variable("L")
  let h = variable("H")
  let t = variable("T")
  let l2 = variable("L")
  let r = variable("R")
  [
    fact(compound("append", [empty_list(), l, l])),
    rule(
      compound("append", [cons(h, t), l2, cons(h, r)]),
      compound("append", [t, l2, r]),
    ),
  ]
}

///|
/// `length([], 0).` and
/// `length([_ | T], N) :- length(T, N1), N is N1 + 1.`
fn length_clauses() -> Array[Clause] {
  let t = variable("T")
  let n = variable("N")
  let n1 = variable("N1")
  [
    fact(compound("length", [empty_list(), Int(0)])),
    rule(
      compound("length", [cons(variable("_"), t), n]),
      and_(compound("length", [t, n1]), is_(n, Compound("+", [n1, Int(1)]))),
    ),
  ]
}

///|
/// `reverse([], []).` and
/// `reverse([H | T], R) :- reverse(T, R1), append(R1, [H], R).`
fn reverse_clauses() -> Array[Clause] {
  let h = variable("H")
  let t = variable("T")
  let r = variable("R")
  let r1 = variable("R1")
  [
    fact(compound("reverse", [empty_list(), empty_list()])),
    rule(
      compound("reverse", [h | t, r]),
      and_(
        compound("reverse", [t, r1]),
        compound("append", [r1, cons(h, empty_list()), r]),
      ),
    ),
  ]
}

///|
/// `between(L, U, X) :- X = L, L =< U.` and
/// `between(L, U, X) :- L < U, L1 is L + 1, between(L1, U, X).`
fn between_clauses() -> Array[Clause] {
  let l = variable("L")
  let u = variable("U")
  let x = variable("X")
  let l1 = variable("L1")
  [
    rule(compound("between", [l, u, x]), and_(eq(x, l), Compound("<=", [l, u]))),
    rule(
      compound("between", [l, u, x]),
      and_(
        and_(Compound("<", [l, u]), is_(l1, Compound("+", [l, Int(1)]))),
        compound("between", [l1, u, x]),
      ),
    ),
  ]
}
