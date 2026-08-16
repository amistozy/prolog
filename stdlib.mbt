///|
/// A small library of classic list / arithmetic predicates, implemented as
/// ordinary Prolog clauses so they stay fully relational (usable in any
/// argument direction):
///
/// - `member/2`, `append/3`, `length/2`, `reverse/2`, `between/3`
/// - `nth0/3`, `nth1/3`, `last/2`, `sum_list/2`, `max_list/2`, `min_list/2`
/// - `select/3`, `flatten/2`, `permutation/2`
/// - `maplist/2..4`, `foldl/4`, `memberchk/2`, `selectchk/3` (need `call/2+`)
/// - `succ/2`, `plus/3`, `numlist/3`, `prefix/2`, `suffix/2`, `same_length/2`
///
/// ```mbt check
/// test {
///   let p = Program::stdlib()
///   let x = variable("X")
///   let answers = p
///     .solve([compound("member", [x, list([int(1), int(2), int(3)])])])
///     .to_array()
///   assert_eq(answers.length(), 3)
///   assert_eq(answers[0].to_string(), "X = 1")
///   assert_eq(answers[2].to_string(), "X = 3")
/// }
/// ```
pub fn Program::stdlib() -> Program {
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
  for c in nth_clauses() {
    clauses.push(c)
  }
  for c in last_clauses() {
    clauses.push(c)
  }
  for c in sum_list_clauses() {
    clauses.push(c)
  }
  for c in max_list_clauses() {
    clauses.push(c)
  }
  for c in min_list_clauses() {
    clauses.push(c)
  }
  for c in select_clauses() {
    clauses.push(c)
  }
  for c in flatten_clauses() {
    clauses.push(c)
  }
  for c in permutation_clauses() {
    clauses.push(c)
  }
  for c in maplist_clauses() {
    clauses.push(c)
  }
  for c in foldl_clauses() {
    clauses.push(c)
  }
  for c in memberchk_clauses() {
    clauses.push(c)
  }
  for c in selectchk_clauses() {
    clauses.push(c)
  }
  for c in succ_clauses() {
    clauses.push(c)
  }
  for c in plus_clauses() {
    clauses.push(c)
  }
  for c in numlist_clauses() {
    clauses.push(c)
  }
  for c in prefix_suffix_clauses() {
    clauses.push(c)
  }
  for c in same_length_clauses() {
    clauses.push(c)
  }
  try! Program(clauses)
}

///|
/// `member(X, [X | _]).` and `member(X, [_ | T]) :- member(X, T).`
fn member_clauses() -> Array[Clause] {
  let x = variable("X")
  let t = variable("T")
  let x2 = variable("X")
  let t2 = variable("T")
  [
    Clause::fact(compound("member", [x, cons(x, t)])),
    Clause(
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
    Clause::fact(compound("append", [empty_list(), l, l])),
    Clause(
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
    Clause::fact(compound("length", [empty_list(), Int(0)])),
    Clause(
      compound("length", [cons(variable("_"), t), n]),
      compound("length", [t, n1]).and_(n.is_(Compound("+", [n1, Int(1)]))),
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
    Clause::fact(compound("reverse", [empty_list(), empty_list()])),
    Clause(
      compound("reverse", [h | t, r]),
      compound("reverse", [t, r1]).and_(
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
    Clause(compound("between", [l, u, x]), x.eq(l).and_(Compound("<=", [l, u]))),
    Clause(
      compound("between", [l, u, x]),
      Compound("<", [l, u])
      .and_(l1.is_(Compound("+", [l, Int(1)])))
      .and_(compound("between", [l1, u, x])),
    ),
  ]
}

///|
/// `nth0(0, [X | _], X).` and
/// `nth0(N, [_ | T], X) :- nth0(M, T, X), N is M + 1.`
/// (`nth1/3` is 1-based.)
fn nth_clauses() -> Array[Clause] {
  let i = variable("I")
  let t = variable("T")
  let i2 = variable("I")
  let m = variable("M")
  let t2 = variable("T")
  let x2 = variable("X")
  let i3 = variable("I")
  let i4 = variable("I")
  let m2 = variable("M")
  let t4 = variable("T")
  let x4 = variable("X")
  [
    Clause::fact(compound("nth0", [int(0), cons(i, t), i])),
    Clause(
      compound("nth0", [i2, cons(variable("_"), t2), x2]),
      compound("nth0", [m, t2, x2]).and_(i2.is_(Compound("+", [m, Int(1)]))),
    ),
    Clause::fact(compound("nth1", [int(1), cons(i3, t), i3])),
    Clause(
      compound("nth1", [i4, cons(variable("_"), t4), x4]),
      compound("nth1", [m2, t4, x4]).and_(i4.is_(Compound("+", [m2, Int(1)]))),
    ),
  ]
}

///|
/// `last([X], X).` and `last([_ | T], X) :- last(T, X).`
fn last_clauses() -> Array[Clause] {
  let x = variable("X")
  let t = variable("T")
  let x2 = variable("X")
  [
    Clause::fact(compound("last", [cons(x, empty_list()), x])),
    Clause(
      compound("last", [cons(variable("_"), t), x2]),
      compound("last", [t, x2]),
    ),
  ]
}

///|
/// `sum_list([], 0).` and `sum_list([X | T], S) :- sum_list(T, S1), S is S1 + X.`
fn sum_list_clauses() -> Array[Clause] {
  let x = variable("X")
  let t = variable("T")
  let s = variable("S")
  let s1 = variable("S1")
  [
    Clause::fact(compound("sum_list", [empty_list(), int(0)])),
    Clause(
      compound("sum_list", [cons(x, t), s]),
      compound("sum_list", [t, s1]).and_(s.is_(Compound("+", [s1, x]))),
    ),
  ]
}

///|
/// `max_list([X], X).` and
/// `max_list([X | T], M) :- max_list(T, M1), M is max(X, M1).`
fn max_list_clauses() -> Array[Clause] {
  let x = variable("X")
  let t = variable("T")
  let m = variable("M")
  let m1 = variable("M1")
  [
    Clause::fact(compound("max_list", [cons(x, empty_list()), x])),
    Clause(
      compound("max_list", [cons(x, t), m]),
      compound("max_list", [t, m1]).and_(m.is_(Compound("max", [x, m1]))),
    ),
  ]
}

///|
/// `min_list([X], X).` and
/// `min_list([X | T], M) :- min_list(T, M1), M is min(X, M1).`
fn min_list_clauses() -> Array[Clause] {
  let x = variable("X")
  let t = variable("T")
  let m = variable("M")
  let m1 = variable("M1")
  [
    Clause::fact(compound("min_list", [cons(x, empty_list()), x])),
    Clause(
      compound("min_list", [cons(x, t), m]),
      compound("min_list", [t, m1]).and_(m.is_(Compound("min", [x, m1]))),
    ),
  ]
}

///|
/// `select(X, [X | T], T).` and
/// `select(X, [H | T], [H | R]) :- select(X, T, R).`
fn select_clauses() -> Array[Clause] {
  let x = variable("X")
  let t = variable("T")
  let h = variable("H")
  let x2 = variable("X")
  let t2 = variable("T")
  let r = variable("R")
  [
    Clause::fact(compound("select", [x, cons(x, t), t])),
    Clause(
      compound("select", [x2, cons(h, t2), cons(h, r)]),
      compound("select", [x2, t2, r]),
    ),
  ]
}

///|
/// `flatten([], []).` and `flatten([H | T], F) :-
/// flatten(H, F1), flatten(T, F2), append(F1, F2, F).`
/// plus `flatten(X, [X]) :- atomic(X).`
fn flatten_clauses() -> Array[Clause] {
  let h = variable("H")
  let t = variable("T")
  let f = variable("F")
  let f1 = variable("F1")
  let f2 = variable("F2")
  let x = variable("X")
  [
    Clause::fact(compound("flatten", [empty_list(), empty_list()])),
    Clause(
      compound("flatten", [cons(h, t), f]),
      compound("flatten", [h, f1])
      .and_(compound("flatten", [t, f2]))
      .and_(compound("append", [f1, f2, f])),
    ),
    Clause(
      compound("flatten", [x, cons(x, empty_list())]),
      compound("atomic", [x]),
    ),
  ]
}

///|
/// `permutation([], []).` and
/// `permutation(L, [H | T]) :- select(H, L, R), permutation(R, T).`
fn permutation_clauses() -> Array[Clause] {
  let h = variable("H")
  let l = variable("L")
  let t = variable("T")
  let r = variable("R")
  [
    Clause::fact(compound("permutation", [empty_list(), empty_list()])),
    Clause(
      compound("permutation", [l, cons(h, t)]),
      compound("select", [h, l, r]).and_(compound("permutation", [r, t])),
    ),
  ]
}

///|
/// `maplist(P, Xs)`, `maplist(P, Xs, Ys)`, `maplist(P, Xs, Ys, Zs)`: applies
/// `P` elementwise (via `call/N`), cf. Scryer's `lists.pl`.
fn maplist_clauses() -> Array[Clause] {
  let p = variable("P")
  let x = variable("X")
  let xs = variable("Xs")
  let y = variable("Y")
  let ys = variable("Ys")
  let z = variable("Z")
  let zs = variable("Zs")
  [
    Clause::fact(compound("maplist", [p, empty_list()])),
    Clause(
      compound("maplist", [p, cons(x, xs)]),
      compound("call", [p, x]).and_(compound("maplist", [p, xs])),
    ),
    Clause::fact(compound("maplist", [p, empty_list(), empty_list()])),
    Clause(
      compound("maplist", [p, cons(x, xs), cons(y, ys)]),
      compound("call", [p, x, y]).and_(compound("maplist", [p, xs, ys])),
    ),
    Clause::fact(
      compound("maplist", [p, empty_list(), empty_list(), empty_list()]),
    ),
    Clause(
      compound("maplist", [p, cons(x, xs), cons(y, ys), cons(z, zs)]),
      compound("call", [p, x, y, z]).and_(compound("maplist", [p, xs, ys, zs])),
    ),
  ]
}

///|
/// `foldl(G, [X | Xs], A0, A) :- call(G, X, A0, A1), foldl(G, Xs, A1, A).`
fn foldl_clauses() -> Array[Clause] {
  let g = variable("G")
  let a = variable("A")
  let x = variable("X")
  let xs = variable("Xs")
  let a0 = variable("A0")
  let a1 = variable("A1")
  [
    Clause::fact(compound("foldl", [g, empty_list(), a, a])),
    Clause(
      compound("foldl", [g, cons(x, xs), a0, a]),
      compound("call", [g, x, a0, a1]).and_(compound("foldl", [g, xs, a1, a])),
    ),
  ]
}

///|
/// `memberchk(X, Xs) :- member(X, Xs), !.` — one solution only.
fn memberchk_clauses() -> Array[Clause] {
  let x = variable("X")
  let xs = variable("Xs")
  [
    Clause(
      compound("memberchk", [x, xs]),
      compound("member", [x, xs]).and_(atom("!")),
    ),
  ]
}

///|
/// `selectchk(X, Xs, Ys) :- select(X, Xs, Ys), !.` — one solution only.
fn selectchk_clauses() -> Array[Clause] {
  let x = variable("X")
  let xs = variable("Xs")
  let ys = variable("Ys")
  [
    Clause(
      compound("selectchk", [x, xs, ys]),
      compound("select", [x, xs, ys]).and_(atom("!")),
    ),
  ]
}

///|
/// `succ(I, S)`: `S` is the successor of the non-negative integer `I`
/// (relational, at least one argument must be instantiated), cf. Scryer's
/// `iso_ext.pl`.
fn succ_clauses() -> Array[Clause] {
  let i = variable("I")
  let s = variable("S")
  [
    // succ(I, S) :- integer(S), !, S > 0, I is S - 1.
    Clause(
      compound("succ", [i, s]),
      compound("integer", [s])
      .and_(atom("!"))
      .and_(Compound(">", [s, int(0)]))
      .and_(i.is_(Compound("-", [s, int(1)]))),
    ),
    // succ(I, S) :- integer(I), !, S is I + 1.
    Clause(
      compound("succ", [i, s]),
      compound("integer", [i])
      .and_(atom("!"))
      .and_(s.is_(Compound("+", [i, int(1)]))),
    ),
  ]
}

///|
/// `plus(A, B, C)`: relational integer addition — with two arguments
/// instantiated, the third is computed.
fn plus_clauses() -> Array[Clause] {
  let a = variable("A")
  let b = variable("B")
  let c = variable("C")
  [
    Clause(
      compound("plus", [a, b, c]),
      compound("integer", [a])
      .and_(compound("integer", [b]))
      .and_(atom("!"))
      .and_(c.is_(Compound("+", [a, b]))),
    ),
    Clause(
      compound("plus", [a, b, c]),
      compound("integer", [a])
      .and_(compound("integer", [c]))
      .and_(atom("!"))
      .and_(b.is_(Compound("-", [c, a]))),
    ),
    Clause(
      compound("plus", [a, b, c]),
      compound("integer", [b])
      .and_(compound("integer", [c]))
      .and_(atom("!"))
      .and_(a.is_(Compound("-", [c, b]))),
    ),
  ]
}

///|
/// `numlist(L, U, Ns)`: `Ns` is the list `[L, ..., U]` (both bounds must be
/// instantiated).
fn numlist_clauses() -> Array[Clause] {
  let l = variable("L")
  let u = variable("U")
  let ns = variable("Ns")
  let l2 = variable("L2")
  let u2 = variable("U2")
  let ns2 = variable("Ns2")
  let l1 = variable("L1")
  [
    Clause(
      compound("numlist", [l, u, ns]),
      compound("integer", [l])
      .and_(compound("integer", [u]))
      .and_(Compound("=<", [l, u]))
      .and_(compound("numlist_", [l, u, ns])),
    ),
    Clause::fact(compound("numlist_", [u, u, cons(u, empty_list())])),
    Clause(
      compound("numlist_", [l2, u2, cons(l2, ns2)]),
      Compound("<", [l2, u2])
      .and_(l1.is_(Compound("+", [l2, int(1)])))
      .and_(compound("numlist_", [l1, u2, ns2])),
    ),
  ]
}

///|
/// `prefix(Pre, Xs) :- append(Pre, _, Xs).` and
/// `suffix(Suf, Xs) :- append(_, Suf, Xs).`
fn prefix_suffix_clauses() -> Array[Clause] {
  let pre = variable("Pre")
  let xs = variable("Xs")
  let suf = variable("Suf")
  let ys = variable("Ys")
  [
    Clause(
      compound("prefix", [pre, xs]),
      compound("append", [pre, variable("_"), xs]),
    ),
    Clause(
      compound("suffix", [suf, ys]),
      compound("append", [variable("_"), suf, ys]),
    ),
  ]
}

///|
/// `same_length([], []).` and
/// `same_length([_ | Xs], [_ | Ys]) :- same_length(Xs, Ys).`
fn same_length_clauses() -> Array[Clause] {
  let xs = variable("Xs")
  let ys = variable("Ys")
  [
    Clause::fact(compound("same_length", [empty_list(), empty_list()])),
    Clause(
      compound("same_length", [cons(variable("_"), xs), cons(variable("_"), ys)]),
      compound("same_length", [xs, ys]),
    ),
  ]
}
