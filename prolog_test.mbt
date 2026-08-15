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
  program,
  fact,
  rule,
  and_,
  or_,
  eq,
  neq,
  identical,
  not_identical,
  is_,
  not_,
  solve,
  solve_first,
  stdlib,
  type PrologError,
}

///|
test "term construction and rendering" {
  let x = variable("X")
  assert_eq(x.to_string(), "X")
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
  // operators: `|` cons (right-nest for chains), `&` conjunction, arithmetic terms
  assert_eq(
    (int(1) | cons(int(2), cons(int(3), empty_list()))).to_string(),
    "[1, 2, 3]",
  )
  assert_eq((x & atom("true")).to_string(), "X, true")
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
  let p = try! program([
    fact(compound("parent", [john, mary])),
    fact(compound("parent", [john, jane])),
    fact(compound("parent", [mary, bob])),
  ])
  // all children of john
  let x = variable("X")
  let answers = solve(p, [compound("parent", [john, x])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "X = mary")
  assert_eq(answers[1].to_string(), "X = jane")
  // conjunction: X is a parent of Y and Y is bob
  let y = variable("Y")
  let conjoined = solve(p, [compound("parent", [x, y]), eq(y, bob)]).to_array()
  assert_eq(conjoined.length(), 1)
  assert_eq(conjoined[0].to_string(), "X = mary, Y = bob")
  // solve_first
  let first = solve_first(p, [compound("parent", [john, x])])
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
  let p = try! program([
    fact(compound("parent", [john, mary])),
    fact(compound("parent", [mary, bob])),
    // ancestor(X, Y) :- parent(X, Y).
    rule(compound("ancestor", [ax, ay]), compound("parent", [ax, ay])),
    // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    rule(
      compound("ancestor", [ax, ay]),
      and_(compound("parent", [ax, az]), compound("ancestor", [az, ay])),
    ),
  ])
  let y2 = variable("Y")
  let answers = solve(p, [compound("ancestor", [john, y2])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "Y = mary")
  assert_eq(answers[1].to_string(), "Y = bob")
  // standardize apart: same query twice gives same results
  let again = solve(p, [compound("ancestor", [john, y2])]).to_array()
  assert_eq(again.length(), 2)
}

///|
test "stdlib: member and append in several directions" {
  let lib = stdlib()
  let x = variable("X")
  // member enumerates
  let m = solve(lib, [compound("member", [x, list([int(1), int(2), int(3)])])]).to_array()
  assert_eq(m.length(), 3)
  assert_eq(m[0].to_string(), "X = 1")
  assert_eq(m[1].to_string(), "X = 2")
  assert_eq(m[2].to_string(), "X = 3")
  // member with a ground element
  let found = solve(lib, [compound("member", [int(2), list([int(1), int(2)])])]).to_array()
  assert_eq(found.length(), 1)
  // member of an empty list fails
  let none = solve(lib, [compound("member", [x, empty_list()])]).to_array()
  assert_eq(none.length(), 0)
  // append, all three directions
  let a = variable("A")
  let b = variable("B")
  let c = variable("C")
  let ap1 = solve(lib, [compound("append", [list([int(1)]), list([int(2)]), c])]).to_array()
  assert_eq(ap1.length(), 1)
  assert_eq(ap1[0].to_string(), "C = [1, 2]")
  let ap2 = solve(lib, [compound("append", [a, b, list([int(1), int(2)])])]).to_array()
  assert_eq(ap2.length(), 3)
  assert_eq(ap2[0].to_string(), "A = [], B = [1, 2]")
  assert_eq(ap2[1].to_string(), "A = [1], B = [2]")
  assert_eq(ap2[2].to_string(), "A = [1, 2], B = []")
  // append with a partial first argument
  let t = variable("T")
  let ap3 = solve(lib, [
    compound("append", [cons(int(1), t), list([int(2)]), list([int(1), int(2)])]),
  ]).to_array()
  assert_eq(ap3.length(), 1)
  assert_eq(ap3[0].to_string(), "T = []")
}

///|
test "stdlib: length, reverse, between" {
  let lib = stdlib()
  let n = variable("N")
  let len = solve(lib, [compound("length", [list([atom("a"), atom("b")]), n])]).to_array()
  assert_eq(len.length(), 1)
  assert_eq(len[0].to_string(), "N = 2")
  // length generates lists; length(L, 2) has exactly one solution
  let l = variable("L")
  let gen = solve(lib, [compound("length", [l, int(2)])]).take(1).to_array()
  assert_eq(gen.length(), 1)
  assert_eq(gen[0].to_string(), "L = [_, _]")
  // reverse
  let r = variable("R")
  let rev = solve(lib, [
    compound("reverse", [list([int(1), int(2), int(3)]), r]),
  ]).to_array()
  assert_eq(rev.length(), 1)
  assert_eq(rev[0].to_string(), "R = [3, 2, 1]")
  // between
  let x = variable("X")
  let bt = solve(lib, [compound("between", [int(1), int(3), x])]).to_array()
  assert_eq(bt.length(), 3)
  assert_eq(bt[0].to_string(), "X = 1")
  assert_eq(bt[1].to_string(), "X = 2")
  assert_eq(bt[2].to_string(), "X = 3")
  let empty = solve(lib, [compound("between", [int(3), int(1), x])]).to_array()
  assert_eq(empty.length(), 0)
}

///|
test "arithmetic: is and comparisons" {
  let p = try! program([])
  let x = variable("X")
  let eval = solve(p, [
    is_(x, compound("*", [compound("+", [int(2), int(3)]), int(4)])),
  ]).to_array()
  assert_eq(eval.length(), 1)
  assert_eq(eval[0].to_string(), "X = 20")
  let flt = solve(p, [is_(x, compound("/", [int(7), int(2)]))]).to_array()
  assert_eq(flt[0].to_string(), "X = 3.5")
  let idiv = solve(p, [is_(x, compound("//", [int(7), int(2)]))]).to_array()
  assert_eq(idiv[0].to_string(), "X = 3")
  let flr = solve(p, [is_(x, compound("div", [int(-7), int(2)]))]).to_array()
  assert_eq(flr[0].to_string(), "X = -4")
  let m = solve(p, [is_(x, compound("mod", [int(-7), int(2)]))]).to_array()
  assert_eq(m[0].to_string(), "X = 1")
  let neg = solve(p, [is_(x, -int(5))]).to_array()
  assert_eq(neg[0].to_string(), "X = -5")
  // comparisons
  let lt = solve(p, [compound("<", [int(1), int(2)])]).to_array()
  assert_eq(lt.length(), 1)
  let le = solve(p, [compound("=<", [int(2), int(2)])]).to_array()
  assert_eq(le.length(), 1)
  let gt = solve(p, [compound(">", [int(1), int(2)])]).to_array()
  assert_eq(gt.length(), 0)
  // is fails on unbound arithmetic
  let bad = solve(p, [is_(x, compound("+", [x, int(1)]))]).to_array()
  assert_eq(bad.length(), 0)
}

///|
test "unification builtins: equal, neq, identical, not identical" {
  let p = try! program([])
  let x = variable("X")
  let y = variable("Y")
  let eq1 = solve(p, [eq(x, atom("a"))]).to_array()
  assert_eq(eq1.length(), 1)
  assert_eq(eq1[0].to_string(), "X = a")
  let eq2 = solve(p, [eq(x, y)]).to_array()
  assert_eq(eq2[0].to_string(), "X = Y")
  let eq3 = solve(p, [eq(int(1), float(1.0))]).to_array()
  assert_eq(eq3.length(), 1)
  let neq_ans = solve(p, [neq(atom("a"), atom("b"))]).to_array()
  assert_eq(neq_ans.length(), 1)
  let neq2 = solve(p, [neq(x, atom("b"))]).to_array()
  assert_eq(neq2.length(), 0)
  let ident = solve(p, [identical(x, x)]).to_array()
  assert_eq(ident.length(), 1)
  let ident2 = solve(p, [identical(x, y)]).to_array()
  assert_eq(ident2.length(), 0)
  let nident = solve(p, [not_identical(x, y)]).to_array()
  assert_eq(nident.length(), 1)
  // \= after binding
  let bound = solve(p, [eq(x, atom("a")), neq(x, atom("b"))]).to_array()
  assert_eq(bound.length(), 1)
}

///|
test "negation, disjunction, cut" {
  let john = atom("john")
  let mary = atom("mary")
  let sx = variable("X")
  let sy = variable("Y")
  let p = try! program([
    fact(compound("parent", [john, mary])),
    rule(compound("single_parent", [sx]), not_(compound("parent", [sx, sy]))),
  ])
  let x = variable("X")
  // not: john has a parent -> fails; an unbound atom succeeds
  let n1 = solve(p, [
    compound("parent", [x, mary]),
    not_(compound("parent", [x, variable("_")])),
  ]).to_array()
  assert_eq(n1.length(), 0)
  let n2 = solve(p, [not_(compound("parent", [atom("nobody"), variable("_")]))]).to_array()
  assert_eq(n2.length(), 1)
  let n3 = solve(p, [compound("single_parent", [atom("ann")])]).to_array()
  assert_eq(n3.length(), 1)
  // disjunction
  let d = solve(p, [or_(eq(x, atom("a")), eq(x, atom("b")))]).to_array()
  assert_eq(d.length(), 2)
  assert_eq(d[0].to_string(), "X = a")
  assert_eq(d[1].to_string(), "X = b")
  // cut: keep only the first solution of a predicate
  let p2 = try! program([
    fact(compound("choice", [int(1)])),
    fact(compound("choice", [int(2)])),
    fact(compound("choice", [int(3)])),
  ])
  let y = variable("Y")
  let all = solve(p2, [compound("choice", [y])]).to_array()
  assert_eq(all.length(), 3)
  let cut = solve(p2, [compound("choice", [y]), atom("!")]).to_array()
  assert_eq(cut.length(), 1)
  assert_eq(cut[0].to_string(), "Y = 1")
}

///|
test "lazy solutions with an infinite program" {
  // natural numbers: nat(0). nat(s(N)) :- nat(N).
  let n = variable("N")
  let p = try! program([
    fact(compound("nat", [int(0)])),
    rule(compound("nat", [compound("s", [n])]), compound("nat", [n])),
  ])
  let x = variable("X")
  let first3 = solve(p, [compound("nat", [x])]).take(3).to_array()
  assert_eq(first3.length(), 3)
  assert_eq(first3[0].to_string(), "X = 0")
  assert_eq(first3[1].to_string(), "X = s(0)")
  assert_eq(first3[2].to_string(), "X = s(s(0))")
}

///|
test "program validation raises on invalid heads" {
  try program([fact(int(42))]) catch {
    PrologError::InvalidHead(term=t) => assert_eq(t.to_string(), "42")
  } noraise {
    _ => fail("expected InvalidHead")
  }
}

///|
test "type tests" {
  let p = try! program([])
  let x = variable("X")
  let is_var = solve(p, [compound("var", [x])]).to_array()
  assert_eq(is_var.length(), 1)
  let is_atom = solve(p, [compound("atom", [atom("a")])]).to_array()
  assert_eq(is_atom.length(), 1)
  let is_list = solve(p, [compound("list", [empty_list()])]).to_array()
  assert_eq(is_list.length(), 1)
  let is_compound = solve(p, [compound("compound", [compound("f", [int(1)])])]).to_array()
  assert_eq(is_compound.length(), 1)
  let not_list = solve(p, [compound("list", [atom("a")])]).to_array()
  assert_eq(not_list.length(), 0)
}

///|
test "meta predicates: findall, once, forall, repeat" {
  let p = try! program([
    fact(compound("color", [atom("red")])),
    fact(compound("color", [atom("green")])),
    fact(compound("color", [atom("blue")])),
  ])
  // findall collects all solutions with fresh variables
  let x = variable("X")
  let l = variable("L")
  let fa = solve(p, [compound("findall", [x, compound("color", [x]), l])]).to_array()
  assert_eq(fa.length(), 1)
  assert_eq(fa[0].to_string(), "L = [red, green, blue]")
  // findall with an empty solution set
  let none = solve(p, [
    compound("findall", [x, compound("color", [atom("nope")]), l]),
  ]).to_array()
  assert_eq(none[0].to_string(), "L = []")
  // once keeps the first solution
  let once_ans = solve(p, [compound("once", [compound("color", [x])])]).to_array()
  assert_eq(once_ans.length(), 1)
  assert_eq(once_ans[0].to_string(), "X = red")
  // forall succeeds when the action holds for every solution
  let ok = solve(p, [
    compound("forall", [compound("color", [x]), compound("color", [x])]),
  ]).to_array()
  assert_eq(ok.length(), 1)
  let bad = solve(p, [
    compound("forall", [compound("color", [x]), eq(x, atom("red"))]),
  ]).to_array()
  assert_eq(bad.length(), 0)
  // repeat with a cut: take the first repeat
  let rep = solve(p, [compound("repeat", []), eq(x, atom("a")), atom("!")]).to_array()
  assert_eq(rep.length(), 1)
  assert_eq(rep[0].to_string(), "X = a")
}

///|
test "if-then-else" {
  let p = try! program([])
  // (A -> B ; C): A holds -> B
  let t1 = solve(p, [parse_term("(true -> X = 2 ; X = 3)")]).to_array()
  assert_eq(t1.length(), 1)
  assert_eq(t1[0].to_string(), "X = 2")
  // A fails -> C
  let t2 = solve(p, [parse_term("(fail -> X = 2 ; X = 3)")]).to_array()
  assert_eq(t2.length(), 1)
  assert_eq(t2[0].to_string(), "X = 3")
  // soft cut: only the committed branch is kept
  let p2 = try! program([
    fact(compound("c", [int(1)])),
    fact(compound("c", [int(2)])),
  ])
  let t3 = solve(p2, [parse_term("(c(Y) -> true ; true)")]).to_array()
  assert_eq(t3.length(), 1)
  assert_eq(t3[0].to_string(), "Y = 1")
  // -> without else: X = 1 binds X, so the then-branch fails; use a
  // condition that does not bind the answer variable
  let t4 = solve(p, [parse_term("(true -> X = 5)")]).to_array()
  assert_eq(t4.length(), 1)
  assert_eq(t4[0].to_string(), "X = 5")
  let t5 = solve(p, [parse_term("(X = 1 ; X = 2 -> true)")]).to_array()
  assert_eq(t5.length(), 2)
}

///|
test "term manipulation: functor, arg, univ, ground" {
  let p = try! program([])
  let f = variable("F")
  let n = variable("N")
  let a = variable("A")
  let f1 = solve(p, [
    compound("functor", [compound("f", [int(1), int(2)]), f, n]),
  ]).to_array()
  assert_eq(f1[0].to_string(), "F = f, N = 2")
  let f2 = solve(p, [compound("functor", [f, atom("g"), int(3)])]).to_array()
  assert_eq(f2[0].to_string(), "F = g(_, _, _)")
  let a1 = solve(p, [
    compound("arg", [int(2), compound("f", [int(1), int(2)]), a]),
  ]).to_array()
  assert_eq(a1[0].to_string(), "A = 2")
  let a2 = solve(p, [compound("arg", [int(1), list([atom("x"), atom("y")]), a])]).to_array()
  assert_eq(a2[0].to_string(), "A = x")
  let u1 = solve(p, [parse_term("f(a, b) =.. L")]).to_array()
  assert_eq(u1[0].to_string(), "L = [f, a, b]")
  let u2 = solve(p, [parse_term("T =.. [g, 1, 2]")]).to_array()
  assert_eq(u2[0].to_string(), "T = g(1, 2)")
  let u3 = solve(p, [parse_term("x =.. L")]).to_array()
  assert_eq(u3[0].to_string(), "L = [x]")
  let g1 = solve(p, [compound("ground", [compound("f", [int(1)])])]).to_array()
  assert_eq(g1.length(), 1)
  let g2 = solve(p, [compound("ground", [compound("f", [variable("Y")])])]).to_array()
  assert_eq(g2.length(), 0)
}

///|
test "term ordering: compare, sort, msort, at" {
  let p = try! program([])
  let o = variable("O")
  let c1 = solve(p, [compound("compare", [o, int(1), int(2)])]).to_array()
  assert_eq(c1[0].to_string(), "O = <")
  let c2 = solve(p, [compound("compare", [o, atom("b"), atom("a")])]).to_array()
  assert_eq(c2[0].to_string(), "O = >")
  let c3 = solve(p, [
    compound("compare", [o, compound("f", [int(1)]), compound("f", [int(1)])]),
  ]).to_array()
  assert_eq(c3[0].to_string(), "O = =")
  // standard order: numbers < atoms < compounds
  let c4 = solve(p, [compound("compare", [o, int(1), atom("a")])]).to_array()
  assert_eq(c4[0].to_string(), "O = <")
  let s = variable("S")
  let s1 = solve(p, [
    compound("sort", [list([int(3), int(1), int(2), int(1)]), s]),
  ]).to_array()
  assert_eq(s1[0].to_string(), "S = [1, 2, 3]")
  let s2 = solve(p, [
    compound("msort", [list([int(3), int(1), int(2), int(1)]), s]),
  ]).to_array()
  assert_eq(s2[0].to_string(), "S = [1, 1, 2, 3]")
  let lt = solve(p, [parse_term("1 @< 2")]).to_array()
  assert_eq(lt.length(), 1)
  let gt = solve(p, [parse_term("b @> a")]).to_array()
  assert_eq(gt.length(), 1)
}

///|
test "atom operations" {
  let p = try! program([])
  let n = variable("N")
  let al = solve(p, [compound("atom_length", [atom("hello"), n])]).to_array()
  assert_eq(al[0].to_string(), "N = 5")
  let c = variable("C")
  let ac = solve(p, [compound("atom_concat", [atom("foo"), atom("bar"), c])]).to_array()
  assert_eq(ac[0].to_string(), "C = foobar")
  let a = variable("A")
  let b = variable("B")
  let splits = solve(p, [compound("atom_concat", [a, b, atom("ab")])]).to_array()
  assert_eq(splits.length(), 3)
  assert_eq(splits[0].to_string(), "A = , B = ab")
  assert_eq(splits[1].to_string(), "A = a, B = b")
  assert_eq(splits[2].to_string(), "A = ab, B = ")
}

///|
test "extended stdlib: nth, last, sums, select, flatten, permutation" {
  let lib = stdlib()
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
  let p = try! parse_program(src)
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
