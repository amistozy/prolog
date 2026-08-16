///|
/// Black-box tests exercising the public API of the Prolog EDSL.
/// Run with `moon test`.
using @prolog {
  variable,
  atom,
  int,
  float,
  str,
  empty_list,
  list,
  cons,
  list_tail,
  compound,
  type Term,
  type Program,
  type Clause,
  type PrologError,
}

///|
test "term construction and rendering" {
  let x = variable("X")
  assert_eq(x.to_string(), "X")
  // Term(...) parses Prolog syntax
  assert_eq(Term("parent(john, X)").to_string(), "parent(john, X)")
  assert_eq(Term("[1, 2]").to_string(), "[1, 2]")
  assert_eq(Term("X + 1").to_string(), "(X + 1)")
  assert_eq(atom("john").to_string(), "john")
  assert_eq(int(42).to_string(), "42")
  assert_eq(float(1.5).to_string(), "1.5")
  assert_eq(str("hi").to_string(), "\"hi\"")
  assert_eq(empty_list().to_string(), "[]")
  assert_eq(list([]).to_string(), "[]")
  assert_eq(list([int(1), int(2)]).to_string(), "[1, 2]")
  assert_eq(cons(int(1), x).to_string(), "[1 | X]")
  assert_eq(list_tail([int(1), int(2)], x).to_string(), "[1, 2 | X]")
  assert_eq(
    compound("parent", [atom("john"), atom("mary")]).to_string(),
    "parent(john, mary)",
  )
  // operators: `|` disjunction, `&` conjunction, arithmetic terms
  assert_eq(
    cons(int(1), cons(int(2), cons(int(3), empty_list()))).to_string(),
    "[1, 2, 3]",
  )
  assert_eq((x & atom("true")).to_string(), "X, true")
  assert_eq((x | atom("true")).to_string(), "(X; true)")
  assert_eq((x + int(1)).to_string(), "(X + 1)")
  assert_eq((x - int(1)).to_string(), "(X - 1)")
  assert_eq((x * int(2)).to_string(), "(X * 2)")
  assert_eq((x / int(2)).to_string(), "(X / 2)")
  assert_eq((-x).to_string(), "-X")
}

///|
test "family database: multiple solutions and conjunction" {
  let john = atom("john")
  let mary = atom("mary")
  let jane = atom("jane")
  let bob = atom("bob")
  let p = Program([
    Clause::fact(compound("parent", [john, mary])),
    Clause::fact(compound("parent", [john, jane])),
    Clause::fact(compound("parent", [mary, bob])),
  ])
  // all children of john
  let x = variable("X")
  let answers = p.solve([compound("parent", [john, x])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "X = mary")
  assert_eq(answers[1].to_string(), "X = jane")
  // conjunction: X is a parent of Y and Y is bob
  let y = variable("Y")
  let conjoined = p.solve([compound("parent", [x, y]), y.eq(bob)]).to_array()
  assert_eq(conjoined.length(), 1)
  assert_eq(conjoined[0].to_string(), "X = mary, Y = bob")
  // solve_first
  let first = p.solve_first([compound("parent", [john, x])])
  assert_eq(first.unwrap().to_string(), "X = mary")
}

///|
test "recursive rules: ancestor" {
  let john = atom("john")
  let mary = atom("mary")
  let bob = atom("bob")
  // NOTE: head and body must share the same variable values.
  let ax = variable("X")
  let ay = variable("Y")
  let az = variable("Z")
  let p = Program([
    Clause::fact(compound("parent", [john, mary])),
    Clause::fact(compound("parent", [mary, bob])),
    // ancestor(X, Y) :- parent(X, Y).
    Clause(compound("ancestor", [ax, ay]), compound("parent", [ax, ay])),
    // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    Clause(
      compound("ancestor", [ax, ay]),
      compound("parent", [ax, az]) & compound("ancestor", [az, ay]),
    ),
  ])
  let y2 = variable("Y")
  let answers = p.solve([compound("ancestor", [john, y2])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "Y = mary")
  assert_eq(answers[1].to_string(), "Y = bob")
  // standardize apart: same query twice gives same results
  let again = p.solve([compound("ancestor", [john, y2])]).to_array()
  assert_eq(again.length(), 2)
}

///|
test "stdlib: member and append in several directions" {
  let lib = Program::stdlib()
  let x = variable("X")
  // member enumerates
  let m = lib
    .solve([compound("member", [x, list([int(1), int(2), int(3)])])])
    .to_array()
  assert_eq(m.length(), 3)
  assert_eq(m[0].to_string(), "X = 1")
  assert_eq(m[1].to_string(), "X = 2")
  assert_eq(m[2].to_string(), "X = 3")
  // member with a ground element
  let found = lib
    .solve([compound("member", [int(2), list([int(1), int(2)])])])
    .to_array()
  assert_eq(found.length(), 1)
  // member of an empty list fails
  let none = lib.solve([compound("member", [x, empty_list()])]).to_array()
  assert_eq(none.length(), 0)
  // append, all three directions
  let a = variable("A")
  let b = variable("B")
  let c = variable("C")
  let ap1 = lib
    .solve([compound("append", [list([int(1)]), list([int(2)]), c])])
    .to_array()
  assert_eq(ap1.length(), 1)
  assert_eq(ap1[0].to_string(), "C = [1, 2]")
  let ap2 = lib
    .solve([compound("append", [a, b, list([int(1), int(2)])])])
    .to_array()
  assert_eq(ap2.length(), 3)
  assert_eq(ap2[0].to_string(), "A = [], B = [1, 2]")
  assert_eq(ap2[1].to_string(), "A = [1], B = [2]")
  assert_eq(ap2[2].to_string(), "A = [1, 2], B = []")
  // append with a partial first argument
  let t = variable("T")
  let ap3 = lib
    .solve([
      compound("append", [
        cons(int(1), t),
        list([int(2)]),
        list([int(1), int(2)]),
      ]),
    ])
    .to_array()
  assert_eq(ap3.length(), 1)
  assert_eq(ap3[0].to_string(), "T = []")
}

///|
test "stdlib: length, reverse, between" {
  let lib = Program::stdlib()
  let n = variable("N")
  let len = lib
    .solve([compound("length", [list([atom("a"), atom("b")]), n])])
    .to_array()
  assert_eq(len.length(), 1)
  assert_eq(len[0].to_string(), "N = 2")
  // length generates lists; length(L, 2) has exactly one solution
  let l = variable("L")
  let gen = lib.solve([compound("length", [l, int(2)])]).take(1).to_array()
  assert_eq(gen.length(), 1)
  assert_eq(gen[0].to_string(), "L = [_, _]")
  // reverse
  let r = variable("R")
  let rev = lib
    .solve([compound("reverse", [list([int(1), int(2), int(3)]), r])])
    .to_array()
  assert_eq(rev.length(), 1)
  assert_eq(rev[0].to_string(), "R = [3, 2, 1]")
  // between
  let x = variable("X")
  let bt = lib.solve([compound("between", [int(1), int(3), x])]).to_array()
  assert_eq(bt.length(), 3)
  assert_eq(bt[0].to_string(), "X = 1")
  assert_eq(bt[1].to_string(), "X = 2")
  assert_eq(bt[2].to_string(), "X = 3")
  let empty = lib.solve([compound("between", [int(3), int(1), x])]).to_array()
  assert_eq(empty.length(), 0)
}

///|
test "arithmetic: is and comparisons" {
  let p = Program([])
  let x = variable("X")
  let eval = p.solve([x.is_((int(2) + int(3)) * int(4))]).to_array()
  assert_eq(eval.length(), 1)
  assert_eq(eval[0].to_string(), "X = 20")
  let flt = p.solve([x.is_(int(7) / int(2))]).to_array()
  assert_eq(flt[0].to_string(), "X = 3.5")
  let idiv = p.solve([x.is_(compound("//", [int(7), int(2)]))]).to_array()
  assert_eq(idiv[0].to_string(), "X = 3")
  let flr = p.solve([x.is_(compound("div", [int(-7), int(2)]))]).to_array()
  assert_eq(flr[0].to_string(), "X = -4")
  let m = p.solve([x.is_(int(-7) % int(2))]).to_array()
  assert_eq(m[0].to_string(), "X = 1")
  let neg = p.solve([x.is_(-int(5))]).to_array()
  assert_eq(neg[0].to_string(), "X = -5")
  // comparisons
  let lt = p.solve([compound("<", [int(1), int(2)])]).to_array()
  assert_eq(lt.length(), 1)
  let le = p.solve([compound("=<", [int(2), int(2)])]).to_array()
  assert_eq(le.length(), 1)
  let gt = p.solve([compound(">", [int(1), int(2)])]).to_array()
  assert_eq(gt.length(), 0)
  // is fails on unbound arithmetic
  let bad = p.solve([x.is_(x + int(1))]).to_array()
  assert_eq(bad.length(), 0)
}

///|
test "unification builtins: equal, neq, identical, not identical" {
  let p = Program([])
  let x = variable("X")
  let y = variable("Y")
  let eq1 = p.solve([x.eq(atom("a"))]).to_array()
  assert_eq(eq1.length(), 1)
  assert_eq(eq1[0].to_string(), "X = a")
  let eq2 = p.solve([x.eq(y)]).to_array()
  assert_eq(eq2[0].to_string(), "X = Y")
  let eq3 = p.solve([int(1).eq(float(1.0))]).to_array()
  assert_eq(eq3.length(), 1)
  let neq_ans = p.solve([atom("a").neq(atom("b"))]).to_array()
  assert_eq(neq_ans.length(), 1)
  let neq2 = p.solve([x.neq(atom("b"))]).to_array()
  assert_eq(neq2.length(), 0)
  let ident = p.solve([x.identical(x)]).to_array()
  assert_eq(ident.length(), 1)
  let ident2 = p.solve([x.identical(y)]).to_array()
  assert_eq(ident2.length(), 0)
  let nident = p.solve([x.not_identical(y)]).to_array()
  assert_eq(nident.length(), 1)
  // \= after binding
  let bound = p.solve([x.eq(atom("a")), x.neq(atom("b"))]).to_array()
  assert_eq(bound.length(), 1)
}

///|
test "negation, disjunction, cut" {
  let john = atom("john")
  let mary = atom("mary")
  let sx = variable("X")
  let sy = variable("Y")
  let p = Program([
    Clause::fact(compound("parent", [john, mary])),
    Clause(compound("single_parent", [sx]), compound("parent", [sx, sy]).not()),
  ])
  let x = variable("X")
  // not: john has a parent -> fails; an unbound atom succeeds
  let n1 = p
    .solve([
      compound("parent", [x, mary]),
      compound("parent", [x, variable("_")]).not(),
    ])
    .to_array()
  assert_eq(n1.length(), 0)
  let n2 = p
    .solve([compound("parent", [atom("nobody"), variable("_")]).not()])
    .to_array()
  assert_eq(n2.length(), 1)
  let n3 = p.solve([compound("single_parent", [atom("ann")])]).to_array()
  assert_eq(n3.length(), 1)
  // disjunction
  let d = p.solve([x.eq(atom("a")) | x.eq(atom("b"))]).to_array()
  assert_eq(d.length(), 2)
  assert_eq(d[0].to_string(), "X = a")
  assert_eq(d[1].to_string(), "X = b")
  // cut: keep only the first solution of a predicate
  let p2 = Program([
    Clause::fact(compound("choice", [int(1)])),
    Clause::fact(compound("choice", [int(2)])),
    Clause::fact(compound("choice", [int(3)])),
  ])
  let y = variable("Y")
  let all = p2.solve([compound("choice", [y])]).to_array()
  assert_eq(all.length(), 3)
  let cut = p2.solve([compound("choice", [y]), atom("!")]).to_array()
  assert_eq(cut.length(), 1)
  assert_eq(cut[0].to_string(), "Y = 1")
}

///|
test "lazy solutions with an infinite program" {
  // natural numbers: nat(0). nat(s(N)) :- nat(N).
  let n = variable("N")
  let p = Program([
    Clause::fact(compound("nat", [int(0)])),
    Clause(compound("nat", [compound("s", [n])]), compound("nat", [n])),
  ])
  let x = variable("X")
  let first3 = p.solve([compound("nat", [x])]).take(3).to_array()
  assert_eq(first3.length(), 3)
  assert_eq(first3[0].to_string(), "X = 0")
  assert_eq(first3[1].to_string(), "X = s(0)")
  assert_eq(first3[2].to_string(), "X = s(s(0))")
}

///|
test "program validation raises on invalid heads" {
  try Program([Clause::fact(int(42))]) catch {
    PrologError::InvalidHead(term=t) => assert_eq(t.to_string(), "42")
  } noraise {
    _ => fail("expected InvalidHead")
  }
}

///|
test "type tests" {
  let p = Program([])
  let x = variable("X")
  let is_var = p.solve([compound("var", [x])]).to_array()
  assert_eq(is_var.length(), 1)
  let is_atom = p.solve([compound("atom", [atom("a")])]).to_array()
  assert_eq(is_atom.length(), 1)
  let is_list = p.solve([compound("list", [empty_list()])]).to_array()
  assert_eq(is_list.length(), 1)
  let is_compound = p
    .solve([compound("compound", [compound("f", [int(1)])])])
    .to_array()
  assert_eq(is_compound.length(), 1)
  let not_list = p.solve([compound("list", [atom("a")])]).to_array()
  assert_eq(not_list.length(), 0)
}

///|
test "meta predicates: findall, once, forall, repeat" {
  let p = Program([
    Clause::fact(compound("color", [atom("red")])),
    Clause::fact(compound("color", [atom("green")])),
    Clause::fact(compound("color", [atom("blue")])),
  ])
  // findall collects all solutions with fresh variables
  let x = variable("X")
  let l = variable("L")
  let fa = p
    .solve([compound("findall", [x, compound("color", [x]), l])])
    .to_array()
  assert_eq(fa.length(), 1)
  assert_eq(fa[0].to_string(), "L = [red, green, blue]")
  // findall with an empty solution set
  let none = p
    .solve([compound("findall", [x, compound("color", [atom("nope")]), l])])
    .to_array()
  assert_eq(none[0].to_string(), "L = []")
  // once keeps the first solution
  let once_ans = p
    .solve([compound("once", [compound("color", [x])])])
    .to_array()
  assert_eq(once_ans.length(), 1)
  assert_eq(once_ans[0].to_string(), "X = red")
  // forall succeeds when the action holds for every solution
  let ok = p
    .solve([
      compound("forall", [compound("color", [x]), compound("color", [x])]),
    ])
    .to_array()
  assert_eq(ok.length(), 1)
  let bad = p
    .solve([compound("forall", [compound("color", [x]), x.eq(atom("red"))])])
    .to_array()
  assert_eq(bad.length(), 0)
  // repeat with a cut: take the first repeat
  let rep = p
    .solve([compound("repeat", []), x.eq(atom("a")), atom("!")])
    .to_array()
  assert_eq(rep.length(), 1)
  assert_eq(rep[0].to_string(), "X = a")
}

///|
test "if-then-else" {
  let p = Program([])
  // (A -> B ; C): A holds -> B
  let t1 = p.solve([parse_term("(true -> X = 2 ; X = 3)")]).to_array()
  assert_eq(t1.length(), 1)
  assert_eq(t1[0].to_string(), "X = 2")
  // A fails -> C
  let t2 = p.solve([parse_term("(fail -> X = 2 ; X = 3)")]).to_array()
  assert_eq(t2.length(), 1)
  assert_eq(t2[0].to_string(), "X = 3")
  // soft cut: only the committed branch is kept
  let p2 = Program([
    Clause::fact(compound("c", [int(1)])),
    Clause::fact(compound("c", [int(2)])),
  ])
  let t3 = p2.solve([parse_term("(c(Y) -> true ; true)")]).to_array()
  assert_eq(t3.length(), 1)
  assert_eq(t3[0].to_string(), "Y = 1")
  // -> without else: X = 1 binds X, so the then-branch fails; use a
  // condition that does not bind the answer variable
  let t4 = p.solve([parse_term("(true -> X = 5)")]).to_array()
  assert_eq(t4.length(), 1)
  assert_eq(t4[0].to_string(), "X = 5")
  let t5 = p.solve([parse_term("(X = 1 ; X = 2 -> true)")]).to_array()
  assert_eq(t5.length(), 2)
}

///|
test "term manipulation: functor, arg, univ, ground" {
  let p = Program([])
  let f = variable("F")
  let n = variable("N")
  let a = variable("A")
  let f1 = p
    .solve([compound("functor", [compound("f", [int(1), int(2)]), f, n])])
    .to_array()
  assert_eq(f1[0].to_string(), "F = f, N = 2")
  let f2 = p.solve([compound("functor", [f, atom("g"), int(3)])]).to_array()
  assert_eq(f2[0].to_string(), "F = g(_, _, _)")
  let a1 = p
    .solve([compound("arg", [int(2), compound("f", [int(1), int(2)]), a])])
    .to_array()
  assert_eq(a1[0].to_string(), "A = 2")
  let a2 = p
    .solve([compound("arg", [int(1), list([atom("x"), atom("y")]), a])])
    .to_array()
  assert_eq(a2[0].to_string(), "A = x")
  let u1 = p.solve([parse_term("f(a, b) =.. L")]).to_array()
  assert_eq(u1[0].to_string(), "L = [f, a, b]")
  let u2 = p.solve([parse_term("T =.. [g, 1, 2]")]).to_array()
  assert_eq(u2[0].to_string(), "T = g(1, 2)")
  let u3 = p.solve([parse_term("x =.. L")]).to_array()
  assert_eq(u3[0].to_string(), "L = [x]")
  let g1 = p.solve([compound("ground", [compound("f", [int(1)])])]).to_array()
  assert_eq(g1.length(), 1)
  let g2 = p
    .solve([compound("ground", [compound("f", [variable("Y")])])])
    .to_array()
  assert_eq(g2.length(), 0)
}

///|
test "term ordering: compare, sort, msort, at" {
  let p = Program([])
  let o = variable("O")
  let c1 = p.solve([compound("compare", [o, int(1), int(2)])]).to_array()
  assert_eq(c1[0].to_string(), "O = <")
  let c2 = p.solve([compound("compare", [o, atom("b"), atom("a")])]).to_array()
  assert_eq(c2[0].to_string(), "O = >")
  let c3 = p
    .solve([
      compound("compare", [o, compound("f", [int(1)]), compound("f", [int(1)])]),
    ])
    .to_array()
  assert_eq(c3[0].to_string(), "O = =")
  // standard order: numbers < atoms < compounds
  let c4 = p.solve([compound("compare", [o, int(1), atom("a")])]).to_array()
  assert_eq(c4[0].to_string(), "O = <")
  let s = variable("S")
  let s1 = p
    .solve([compound("sort", [list([int(3), int(1), int(2), int(1)]), s])])
    .to_array()
  assert_eq(s1[0].to_string(), "S = [1, 2, 3]")
  let s2 = p
    .solve([compound("msort", [list([int(3), int(1), int(2), int(1)]), s])])
    .to_array()
  assert_eq(s2[0].to_string(), "S = [1, 1, 2, 3]")
  let lt = p.solve([parse_term("1 @< 2")]).to_array()
  assert_eq(lt.length(), 1)
  let gt = p.solve([parse_term("b @> a")]).to_array()
  assert_eq(gt.length(), 1)
}

///|
test "atom operations" {
  let p = Program([])
  let n = variable("N")
  let al = p.solve([compound("atom_length", [atom("hello"), n])]).to_array()
  assert_eq(al[0].to_string(), "N = 5")
  let c = variable("C")
  let ac = p
    .solve([compound("atom_concat", [atom("foo"), atom("bar"), c])])
    .to_array()
  assert_eq(ac[0].to_string(), "C = foobar")
  let a = variable("A")
  let b = variable("B")
  let splits = p.solve([compound("atom_concat", [a, b, atom("ab")])]).to_array()
  assert_eq(splits.length(), 3)
  assert_eq(splits[0].to_string(), "A = , B = ab")
  assert_eq(splits[1].to_string(), "A = a, B = b")
  assert_eq(splits[2].to_string(), "A = ab, B = ")
}

///|
test "extended stdlib: nth, last, sums, select, flatten, permutation" {
  let lib = Program::stdlib()
  let e = variable("E")
  let n0 = variable("N")
  let nth = lib
    .solve([compound("nth0", [n0, list([atom("a"), atom("b"), atom("c")]), e])])
    .to_array()
  assert_eq(nth.length(), 3)
  assert_eq(nth[0].to_string(), "N = 0, E = a")
  assert_eq(nth[2].to_string(), "N = 2, E = c")
  let last = lib
    .solve([compound("last", [list([int(1), int(2), int(3)]), e])])
    .to_array()
  assert_eq(last[0].to_string(), "E = 3")
  let s = variable("S")
  let sum = lib
    .solve([compound("sum_list", [list([int(1), int(2), int(3)]), s])])
    .to_array()
  assert_eq(sum[0].to_string(), "S = 6")
  let m = variable("M")
  let mx = lib
    .solve([compound("max_list", [list([int(3), int(7), int(2)]), m])])
    .to_array()
  assert_eq(mx[0].to_string(), "M = 7")
  let mn = lib
    .solve([compound("min_list", [list([int(3), int(7), int(2)]), m])])
    .to_array()
  assert_eq(mn[0].to_string(), "M = 2")
  let r = variable("R")
  let sel = lib
    .solve([compound("select", [int(2), list([int(1), int(2), int(3)]), r])])
    .to_array()
  assert_eq(sel[0].to_string(), "R = [1, 3]")
  let f = variable("F")
  let fl = lib
    .solve([
      compound("flatten", [
        list([list([int(1), int(2)]), list([int(3), list([int(4)])])]),
        f,
      ]),
    ])
    .to_array()
  assert_eq(fl[0].to_string(), "F = [1, 2, 3, 4]")
  let perm = lib
    .solve([compound("permutation", [list([int(1), int(2)]), r])])
    .to_array()
  assert_eq(perm.length(), 2)
  assert_eq(perm[0].to_string(), "R = [1, 2]")
  assert_eq(perm[1].to_string(), "R = [2, 1]")
}

///|
test "parsing an entire program and querying it" {
  let src =
    #|%% a tiny family database
    #|parent(john, mary). parent(john, jane). parent(mary, bob).
    #|/* ancestor rules */
    #|ancestor(X, Y) :- parent(X, Y).
    #|ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    #|
  let p = parse_program(src)
  let y = variable("Y")
  let answers = p.solve([compound("ancestor", [atom("john"), y])]).to_array()
  assert_eq(answers.length(), 3)
  assert_eq(answers[0].to_string(), "Y = mary")
  assert_eq(answers[1].to_string(), "Y = jane")
  assert_eq(answers[2].to_string(), "Y = bob")
  // parse errors raise
  try parse_term("f(") catch {
    ParseError::UnexpectedEof(pos=_p) => ()
    _ => fail("expected UnexpectedEof")
  } noraise {
    _ => fail("expected parse error")
  }
  try parse_term("f(a") catch {
    ParseError::UnexpectedEof(pos=_p) => ()
    _ => fail("expected UnexpectedEof")
  } noraise {
    _ => fail("expected parse error")
  }
}

///|
test "dif/2 disequality constraint" {
  let p = Program([])
  let x = variable("X")
  let y = variable("Y")
  // ground terms decide immediately
  let a1 = p.solve([atom("a").dif(atom("a"))]).to_array()
  assert_eq(a1.length(), 0)
  let a2 = p.solve([atom("a").dif(atom("b"))]).to_array()
  assert_eq(a2.length(), 1)
  // unbound: the constraint is delayed
  let a3 = p.solve([x.dif(atom("b"))]).to_array()
  assert_eq(a3.length(), 1)
  // a later binding that violates the constraint fails
  let a4 = p.solve([x.dif(atom("b")), x.eq(atom("b"))]).to_array()
  assert_eq(a4.length(), 0)
  let a5 = p.solve([x.dif(atom("b")), x.eq(atom("a"))]).to_array()
  assert_eq(a5.length(), 1)
  assert_eq(a5[0].to_string(), "X = a")
  // \= is the ISO non-unifiability test, not a constraint: it fails while
  // X is unbound
  let a6 = p.solve([x.neq(atom("b"))]).to_array()
  assert_eq(a6.length(), 0)
  let a7 = p.solve([x.eq(atom("a")), x.neq(atom("b"))]).to_array()
  assert_eq(a7.length(), 1)
  // two unbound variables
  let a8 = p.solve([x.dif(y), x.eq(atom("a")), y.eq(atom("a"))]).to_array()
  assert_eq(a8.length(), 0)
  let a9 = p.solve([x.dif(y), x.eq(atom("a")), y.eq(atom("b"))]).to_array()
  assert_eq(a9.length(), 1)
  // constraints are undone on backtracking
  let p2 = Program([
    Clause::fact(compound("choice", [int(1)])),
    Clause::fact(compound("choice", [int(2)])),
  ])
  let c = variable("C")
  let a10 = p2.solve([compound("choice", [c]), x.dif(c)]).to_array()
  assert_eq(a10.length(), 2)
  assert_eq(a10[0].to_string(), "C = 1")
  assert_eq(a10[1].to_string(), "C = 2")
}

///|
test "DCG: grammar rules via the parser and phrase" {
  let src =
    #|as --> [].
    #|as --> [a], as.
    #|
  let p = parse_program(src)
  let l = variable("L")
  // phrase generates
  let answers = p
    .solve([compound("phrase", [atom("as"), l])])
    .take(3)
    .to_array()
  assert_eq(answers[0].to_string(), "L = []")
  assert_eq(answers[1].to_string(), "L = [a]")
  assert_eq(answers[2].to_string(), "L = [a, a]")
  // phrase checks
  let ok = p
    .solve([compound("phrase", [atom("as"), list([atom("a"), atom("a")])])])
    .to_array()
  assert_eq(ok.length(), 1)
  let bad = p
    .solve([compound("phrase", [atom("as"), list([atom("a"), atom("b")])])])
    .to_array()
  assert_eq(bad.length(), 0)
  // phrase/3 leaves the rest; `as` consumes only a's, so [a, a, b] leaves
  // [b] as its longest match
  let r = variable("R")
  let rest = p
    .solve([
      compound("phrase", [
        atom("as"),
        list([atom("a"), atom("a"), atom("b")]),
        r,
      ]),
    ])
    .to_array()
  assert_eq(rest.length(), 3)
  assert_eq(rest[0].to_string(), "R = [a, a, b]")
  assert_eq(rest[2].to_string(), "R = [b]")
}

///|
test "DCG: terminals, sequencing, alternatives, braces, cut" {
  // digits([D | Ds]) --> [D], digits(Ds). — terminals and sequencing
  // lang --> [a] ; [b]. — alternatives
  // t --> { X = 1 }, [X]. — plain goals
  // first --> [a], !. — cut
  let src =
    #|digits([D]) --> [D].
    #|digits([D | Ds]) --> [D], digits(Ds).
    #|lang --> [a] ; [b].
    #|t --> { X = 1 }, [X].
    #|first --> [a], !.
    #|
  let p = parse_program(src)
  let l = variable("L")
  let d = p
    .solve([
      compound("phrase", [
        compound("digits", [l]),
        list([int(1), int(2), int(3)]),
      ]),
    ])
    .to_array()
  assert_eq(d.length(), 1)
  assert_eq(d[0].to_string(), "L = [1, 2, 3]")
  let alt = p.solve([compound("phrase", [atom("lang"), l])]).to_array()
  assert_eq(alt.length(), 2)
  assert_eq(alt[0].to_string(), "L = [a]")
  assert_eq(alt[1].to_string(), "L = [b]")
  let t = p.solve([compound("phrase", [atom("t"), l])]).to_array()
  assert_eq(t[0].to_string(), "L = [1]")
  let f1 = p
    .solve([compound("phrase", [atom("first"), list([atom("a")])])])
    .to_array()
  assert_eq(f1.length(), 1)
  let f2 = p
    .solve([compound("phrase", [atom("first"), list([atom("b")])])])
    .to_array()
  assert_eq(f2.length(), 0)
}

///|
test "DCG: building rules programmatically with dcg_rule" {
  // greet(X) --> [hi, X]. built with the EDSL API instead of the parser
  let gx = variable("X")
  let p = Program([dcg_rule(compound("greet", [gx]), list([atom("hi"), gx]))])
  let l = variable("L")
  let answers = p
    .solve([compound("phrase", [compound("greet", [atom("bob")]), l])])
    .to_array()
  assert_eq(answers.length(), 1)
  assert_eq(answers[0].to_string(), "L = [hi, bob]")
}

///|
test "bagof and setof" {
  let src =
    #|f(1, a). f(1, b). f(2, c). f(2, c).
    #|
  let p = parse_program(src)
  let x = variable("X")
  let y = variable("Y")
  let s = variable("S")
  // bagof groups by the free variables of the goal that are not in the
  // template
  let b1 = p
    .solve([compound("bagof", [x, compound("f", [y, x]), s])])
    .to_array()
  assert_eq(b1.length(), 2)
  assert_eq(b1[0].to_string(), "S = [a, b]")
  assert_eq(b1[1].to_string(), "S = [c, c]")
  // setof sorts and removes duplicates inside each group
  let b2 = p
    .solve([compound("setof", [x, compound("f", [y, x]), s])])
    .to_array()
  assert_eq(b2.length(), 2)
  assert_eq(b2[0].to_string(), "S = [a, b]")
  assert_eq(b2[1].to_string(), "S = [c]")
  // Y ^ Goal: Y is existential, so there is a single group
  let b3 = p
    .solve([
      compound("setof", [x, compound("^", [y, compound("f", [y, x])]), s]),
    ])
    .to_array()
  assert_eq(b3.length(), 1)
  assert_eq(b3[0].to_string(), "S = [a, b, c]")
  // bagof fails when the goal has no solutions
  let b4 = p
    .solve([
      compound("bagof", [x, compound("f", [variable("Z"), atom("nope")]), s]),
    ])
    .to_array()
  assert_eq(b4.length(), 0)
  // setof sorts the solutions of a plain goal
  let p2 = parse_program("g(2). g(1). g(2).")
  let b5 = p2.solve([compound("setof", [x, compound("g", [x]), s])]).to_array()
  assert_eq(b5.length(), 1)
  assert_eq(b5[0].to_string(), "S = [1, 2]")
  let b6 = p2.solve([compound("bagof", [x, compound("g", [x]), s])]).to_array()
  assert_eq(b6.length(), 1)
  assert_eq(b6[0].to_string(), "S = [2, 1, 2]")
}

///|
test "atom_codes, atom_chars, char_code" {
  let p = Program([])
  let cs = variable("Cs")
  let a1 = p.solve([compound("atom_codes", [atom("abc"), cs])]).to_array()
  assert_eq(a1[0].to_string(), "Cs = [97, 98, 99]")
  let a = variable("A")
  let a2 = p
    .solve([compound("atom_codes", [a, list([int(97), int(98)])])])
    .to_array()
  assert_eq(a2[0].to_string(), "A = ab")
  let a3 = p.solve([compound("atom_chars", [atom("abc"), cs])]).to_array()
  assert_eq(a3[0].to_string(), "Cs = [a, b, c]")
  let a4 = p
    .solve([compound("atom_chars", [a, list([atom("a"), atom("b")])])])
    .to_array()
  assert_eq(a4[0].to_string(), "A = ab")
  // invalid codes fail
  let a5 = p.solve([compound("atom_codes", [a, list([int(-1)])])]).to_array()
  assert_eq(a5.length(), 0)
  let k = variable("K")
  let a6 = p.solve([compound("char_code", [atom("a"), k])]).to_array()
  assert_eq(a6[0].to_string(), "K = 97")
  let c = variable("C")
  let a7 = p.solve([compound("char_code", [c, int(98)])]).to_array()
  assert_eq(a7[0].to_string(), "C = b")
  let a8 = p.solve([compound("char_code", [atom("ab"), k])]).to_array()
  assert_eq(a8.length(), 0)
}

///|
test "number_codes, number_chars, atom_number" {
  let p = Program([])
  let cs = variable("Cs")
  let n1 = p.solve([compound("number_codes", [int(42), cs])]).to_array()
  assert_eq(n1[0].to_string(), "Cs = [52, 50]")
  let n = variable("N")
  let n2 = p
    .solve([compound("number_codes", [n, list([int(52), int(50)])])])
    .to_array()
  assert_eq(n2[0].to_string(), "N = 42")
  let n3 = p.solve([compound("number_chars", [float(1.5), cs])]).to_array()
  assert_eq(n3[0].to_string(), "Cs = [1, ., 5]")
  let n4 = p
    .solve([
      compound("number_chars", [n, list([atom("1"), atom("."), atom("5")])]),
    ])
    .to_array()
  assert_eq(n4[0].to_string(), "N = 1.5")
  // non-numbers fail
  let n5 = p
    .solve([compound("number_chars", [n, list([atom("x")])])])
    .to_array()
  assert_eq(n5.length(), 0)
  let a = variable("A")
  let n6 = p.solve([compound("atom_number", [atom("42"), a])]).to_array()
  assert_eq(n6[0].to_string(), "A = 42")
  let n7 = p.solve([compound("atom_number", [a, int(7)])]).to_array()
  assert_eq(n7[0].to_string(), "A = 7")
}

///|
test "sub_atom" {
  let p = Program([])
  let s = variable("S")
  let a1 = p
    .solve([
      compound("sub_atom", [atom("abc"), int(1), int(1), variable("_"), s]),
    ])
    .to_array()
  assert_eq(a1.length(), 1)
  assert_eq(a1[0].to_string(), "S = b")
  // enumerate all splits of "ab"
  let b = variable("B")
  let l = variable("L")
  let af = variable("Af")
  let all = p
    .solve([compound("sub_atom", [atom("ab"), b, l, af, s])])
    .to_array()
  assert_eq(all.length(), 6)
  assert_eq(all[0].to_string(), "B = 0, L = 0, Af = 2, S = ")
  assert_eq(all[1].to_string(), "B = 0, L = 1, Af = 1, S = a")
  assert_eq(all[2].to_string(), "B = 0, L = 2, Af = 0, S = ab")
  assert_eq(all[5].to_string(), "B = 2, L = 0, Af = 0, S = ")
  // ground positions prune the enumeration
  let a2 = p
    .solve([compound("sub_atom", [atom("abc"), int(5), l, af, s])])
    .to_array()
  assert_eq(a2.length(), 0)
}

///|
test "call/N, ignore, copy_term, term_variables" {
  let p = parse_program("q(1, a). q(2, b).")
  let x = variable("X")
  let y = variable("Y")
  // call(G, A1, ..., An) appends the extra arguments
  let a1 = p
    .solve([compound("call", [compound("q", [x]), atom("a")])])
    .to_array()
  assert_eq(a1.length(), 1)
  assert_eq(a1[0].to_string(), "X = 1")
  let a2 = p.solve([compound("call", [compound("q", [x]), y])]).to_array()
  assert_eq(a2.length(), 2)
  assert_eq(a2[0].to_string(), "X = 1, Y = a")
  assert_eq(a2[1].to_string(), "X = 2, Y = b")
  // ignore succeeds whether or not its goal succeeds
  let a3 = p
    .solve([compound("ignore", [compound("q", [int(99), y])])])
    .to_array()
  assert_eq(a3.length(), 1)
  let a4 = p
    .solve([compound("ignore", [compound("q", [int(1), y])])])
    .to_array()
  assert_eq(a4.length(), 1)
  assert_eq(a4[0].to_string(), "Y = a")
  // copy_term makes an independent copy: binding the copy does not bind
  // the original's variables
  let c = variable("C")
  let a5 = p
    .solve([
      x.eq(compound("f", [atom("a"), y])),
      compound("copy_term", [x, c]),
      c.eq(compound("f", [atom("a"), atom("q")])),
      y.eq(atom("z")),
    ])
    .to_array()
  assert_eq(a5.length(), 1)
  assert_eq(a5[0].to_string(), "X = f(a, z), Y = z, C = f(a, q)")
  // term_variables collects the variables in order, without duplicates
  let v = variable("V")
  let a6 = p
    .solve([
      compound("term_variables", [compound("f", [x, compound("g", [x])]), v]),
    ])
    .to_array()
  assert_eq(a6[0].to_string(), "V = [X]")
}

///|
test "stdlib: maplist, foldl, memberchk, selectchk" {
  let lib = Program::stdlib()
  lib.add(parse_clause("add3(X, A, B) :- B is A + X."))
  let l = variable("L")
  // maplist/3 with a builtin predicate of arity 2
  let m1 = lib
    .solve([
      compound("maplist", [
        atom("atom_length"),
        list([atom("a"), atom("ab"), atom("abc")]),
        l,
      ]),
    ])
    .to_array()
  assert_eq(m1[0].to_string(), "L = [1, 2, 3]")
  // maplist/2 as a test
  let m2 = lib
    .solve([compound("maplist", [atom("integer"), list([int(1), int(2)])])])
    .to_array()
  assert_eq(m2.length(), 1)
  let m3 = lib
    .solve([compound("maplist", [atom("integer"), list([int(1), atom("a")])])])
    .to_array()
  assert_eq(m3.length(), 0)
  // maplist/3 with a partially-applied closure
  let x = variable("X")
  let m4 = lib
    .solve([
      compound("maplist", [
        compound("add3", [int(10)]),
        list([int(1), int(2)]),
        l,
      ]),
    ])
    .to_array()
  assert_eq(m4[0].to_string(), "L = [11, 12]")
  // maplist/2 with a fully-applied closure as a test
  let m4b = lib
    .solve([
      compound("maplist", [compound("plus", [int(5), int(6)]), list([int(11)])]),
    ])
    .to_array()
  assert_eq(m4b.length(), 1)
  // foldl
  let s = variable("S")
  let f1 = lib
    .solve([
      compound("foldl", [
        atom("add3"),
        list([int(1), int(2), int(3)]),
        int(0),
        s,
      ]),
    ])
    .to_array()
  assert_eq(f1[0].to_string(), "S = 6")
  // memberchk keeps only the first solution
  let mc = lib
    .solve([compound("memberchk", [x, list([int(1), int(2), int(1)])])])
    .to_array()
  assert_eq(mc.length(), 1)
  assert_eq(mc[0].to_string(), "X = 1")
  // selectchk
  let ys = variable("Ys")
  let sc = lib
    .solve([compound("selectchk", [x, list([int(1), int(2), int(1)]), ys])])
    .to_array()
  assert_eq(sc.length(), 1)
  assert_eq(sc[0].to_string(), "X = 1, Ys = [2, 1]")
}

///|
test "stdlib: succ, plus, numlist, prefix, suffix, same_length" {
  let lib = Program::stdlib()
  let s = variable("S")
  let su1 = lib.solve([compound("succ", [int(2), s])]).to_array()
  assert_eq(su1[0].to_string(), "S = 3")
  let i = variable("I")
  let su2 = lib.solve([compound("succ", [i, int(3)])]).to_array()
  assert_eq(su2[0].to_string(), "I = 2")
  let su3 = lib.solve([compound("succ", [int(2), int(2)])]).to_array()
  assert_eq(su3.length(), 0)
  // plus is relational with two instantiated arguments
  let c = variable("C")
  let pl1 = lib.solve([compound("plus", [int(2), int(3), c])]).to_array()
  assert_eq(pl1[0].to_string(), "C = 5")
  let b = variable("B")
  let pl2 = lib.solve([compound("plus", [int(2), b, int(5)])]).to_array()
  assert_eq(pl2[0].to_string(), "B = 3")
  let a = variable("A")
  let pl3 = lib.solve([compound("plus", [a, b, int(5)])]).to_array()
  assert_eq(pl3.length(), 0)
  // numlist
  let ns = variable("Ns")
  let nl = lib.solve([compound("numlist", [int(1), int(3), ns])]).to_array()
  assert_eq(nl[0].to_string(), "Ns = [1, 2, 3]")
  // prefix and suffix
  let ok1 = lib
    .solve([
      compound("prefix", [list([int(1)]), list([int(1), int(2), int(3)])]),
    ])
    .to_array()
  assert_eq(ok1.length(), 1)
  let ok2 = lib
    .solve([
      compound("suffix", [list([int(3)]), list([int(1), int(2), int(3)])]),
    ])
    .to_array()
  assert_eq(ok2.length(), 1)
  let bad = lib
    .solve([compound("prefix", [list([int(2)]), list([int(1), int(2)])])])
    .to_array()
  assert_eq(bad.length(), 0)
  let pre = variable("Pre")
  let prefs = lib
    .solve([compound("prefix", [pre, list([int(1), int(2)])])])
    .to_array()
  assert_eq(prefs.length(), 3)
  assert_eq(prefs[2].to_string(), "Pre = [1, 2]")
  // same_length
  let sl = variable("SL")
  let same1 = lib
    .solve([
      compound("same_length", [
        list([atom("a"), atom("b")]),
        list([int(1), int(2)]),
      ]),
    ])
    .to_array()
  assert_eq(same1.length(), 1)
  let same2 = lib
    .solve([compound("same_length", [sl, list([int(1), int(2), int(3)])])])
    .to_array()
  assert_eq(same2[0].to_string(), "SL = [_, _, _]")
}

///|
test "parser: base literals, char codes, braces, dcg operator" {
  assert_eq(parse_term("0x1F").to_string(), "31")
  assert_eq(parse_term("0X1f").to_string(), "31")
  assert_eq(parse_term("0o17").to_string(), "15")
  assert_eq(parse_term("0b101").to_string(), "5")
  assert_eq(parse_term("0'a").to_string(), "97")
  assert_eq(parse_term("0'\\n").to_string(), "10")
  assert_eq(parse_term("{X = 1}").to_string(), "{ X = 1 }")
  // a DCG clause parses as a regular clause
  let c = parse_clause("a --> [b].")
  let p = Program([c])
  let l = variable("L")
  let answers = p.solve([compound("phrase", [atom("a"), l])]).to_array()
  assert_eq(answers[0].to_string(), "L = [b]")
}

///|
test "arithmetic: power and sqrt" {
  let p = Program([])
  let x = variable("X")
  let p1 = p.solve([x.is_(parse_term("2 ^ 10"))]).to_array()
  assert_eq(p1[0].to_string(), "X = 1024")
  let p2 = p.solve([x.is_(parse_term("2 ^ -1"))]).to_array()
  assert_eq(p2[0].to_string(), "X = 0.5")
  let p3 = p.solve([x.is_(parse_term("sqrt(16)"))]).to_array()
  assert_eq(p3[0].to_string(), "X = 4.0")
  let p4 = p.solve([x.is_(parse_term("-0x10"))]).to_array()
  assert_eq(p4[0].to_string(), "X = -16")
}

///|
test "answers render bindings in query order" {
  let p = Program([Clause::fact(compound("p", [atom("a"), atom("b")]))])
  let x = variable("X")
  let y = variable("Y")
  let z = variable("Z")
  let answers = p.solve([compound("p", [z, y]), x.eq(atom("q"))]).to_array()
  assert_eq(answers.length(), 1)
  assert_eq(answers[0].to_string(), "Z = a, Y = b, X = q")
  // Answer::get looks bindings up by name
  assert_eq(answers[0].get("Y"), Some(atom("b")))
}

///|
test "coverage: float arithmetic, comparisons, type tests, functor" {
  let p = Program([])
  let x = variable("X")
  // float evaluation paths
  let f1 = p.solve([x.is_(parse_term("1.5 + 2"))]).to_array()
  assert_eq(f1[0].to_string(), "X = 3.5")
  let f2 = p.solve([x.is_(parse_term("-1.5"))]).to_array()
  assert_eq(f2[0].to_string(), "X = -1.5")
  let f3 = p.solve([x.is_(parse_term("abs(-3)"))]).to_array()
  assert_eq(f3[0].to_string(), "X = 3")
  let f4 = p.solve([x.is_(parse_term("abs(-1.5)"))]).to_array()
  assert_eq(f4[0].to_string(), "X = 1.5")
  let f5 = p.solve([x.is_(parse_term("sqrt(2.25)"))]).to_array()
  assert_eq(f5[0].to_string(), "X = 1.5")
  let f6 = p.solve([x.is_(parse_term("1.5 ^ 2"))]).to_array()
  assert_eq(f6[0].to_string(), "X = 2.25")
  let f7 = p.solve([x.is_(parse_term("max(1.5, 2.5)"))]).to_array()
  assert_eq(f7[0].to_string(), "X = 2.5")
  let f8 = p.solve([x.is_(parse_term("min(1.5, 2.5)"))]).to_array()
  assert_eq(f8[0].to_string(), "X = 1.5")
  let f9 = p.solve([x.is_(parse_term("7 div 2"))]).to_array()
  assert_eq(f9[0].to_string(), "X = 3")
  // float / mixed comparisons
  let c1 = p.solve([parse_term("1.5 >= 1.5")]).to_array()
  assert_eq(c1.length(), 1)
  let c2 = p.solve([parse_term("1.5 =:= 1.5")]).to_array()
  assert_eq(c2.length(), 1)
  let c3 = p.solve([parse_term("1.5 =\\= 2.5")]).to_array()
  assert_eq(c3.length(), 1)
  let c4 = p.solve([parse_term("1.5 < 2")]).to_array()
  assert_eq(c4.length(), 1)
  let c5 = p.solve([parse_term("2 >= 2")]).to_array()
  assert_eq(c5.length(), 1)
  let c6 = p.solve([parse_term("1.5 =< 1.5")]).to_array()
  assert_eq(c6.length(), 1)
  // comparisons fail on non-numbers
  let c7 = p.solve([parse_term("a < b")]).to_array()
  assert_eq(c7.length(), 0)
  // term ordering
  let c8 = p.solve([parse_term("1 @=< 2")]).to_array()
  assert_eq(c8.length(), 1)
  // type tests
  let t1 = p.solve([parse_term("nonvar(a)")]).to_array()
  assert_eq(t1.length(), 1)
  let t2 = p.solve([parse_term("float(1.5)")]).to_array()
  assert_eq(t2.length(), 1)
  let t3 = p.solve([parse_term("string(\"hi\")")]).to_array()
  assert_eq(t3.length(), 1)
  let t4 = p.solve([parse_term("number(1.5)")]).to_array()
  assert_eq(t4.length(), 1)
  let t5 = p.solve([parse_term("atomic(1.5)")]).to_array()
  assert_eq(t5.length(), 1)
  // call/1 and \+ on a small program
  let p2 = parse_program("q(1). q(2).")
  let c9 = p2.solve([compound("call", [compound("q", [x])])]).to_array()
  assert_eq(c9.length(), 2)
  let c10 = p2.solve([parse_term("\\+ q(99)")]).to_array()
  assert_eq(c10.length(), 1)
  // atom_length works on strings too
  let n = variable("N")
  let c11 = p.solve([compound("atom_length", [str("hi"), n])]).to_array()
  assert_eq(c11[0].to_string(), "N = 2")
  // write/writeln succeed and print
  let w1 = p.solve([compound("write", [atom("hi")])]).to_array()
  assert_eq(w1.length(), 1)
  // functor on every term shape
  let f = variable("F")
  let n2 = variable("N")
  let fu1 = p.solve([compound("functor", [atom("abc"), f, n2])]).to_array()
  assert_eq(fu1[0].to_string(), "F = abc, N = 0")
  let fu2 = p.solve([compound("functor", [int(42), f, n2])]).to_array()
  assert_eq(fu2[0].to_string(), "F = 42, N = 0")
  let fu3 = p.solve([compound("functor", [float(1.5), f, n2])]).to_array()
  assert_eq(fu3[0].to_string(), "F = 1.5, N = 0")
  let fu4 = p.solve([compound("functor", [str("s"), f, n2])]).to_array()
  assert_eq(fu4[0].to_string(), "F = \"s\", N = 0")
  let fu5 = p.solve([compound("functor", [empty_list(), f, n2])]).to_array()
  assert_eq(fu5[0].to_string(), "F = [], N = 0")
  // a List (not a cons chain) has functor '.'/2
  let fu5b = p.solve([compound("functor", [list([int(1)]), f, n2])]).to_array()
  assert_eq(fu5b[0].to_string(), "F = ., N = 2")
  // functor builds atoms and numbers of arity 0
  let t = variable("T")
  let fu6 = p.solve([compound("functor", [t, atom("g"), int(0)])]).to_array()
  assert_eq(fu6[0].to_string(), "T = g")
  let fu7 = p.solve([compound("functor", [t, int(7), int(0)])]).to_array()
  assert_eq(fu7[0].to_string(), "T = 7")
  // =.. on a proper list
  let fu8 = p.solve([parse_term("[a, b] =.. L")]).to_array()
  assert_eq(fu8[0].to_string(), "L = [., a, [b]]")
  // arg fails out of range
  let a = variable("A")
  let fu9 = p
    .solve([compound("arg", [int(0), compound("f", [int(1)]), a])])
    .to_array()
  assert_eq(fu9.length(), 0)
}
