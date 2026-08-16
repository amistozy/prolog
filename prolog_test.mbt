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
      compound("parent", [ax, az]).and_(compound("ancestor", [az, ay])),
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
  let eval = p
    .solve([x.is_(compound("*", [compound("+", [int(2), int(3)]), int(4)]))])
    .to_array()
  assert_eq(eval.length(), 1)
  assert_eq(eval[0].to_string(), "X = 20")
  let flt = p.solve([x.is_(compound("/", [int(7), int(2)]))]).to_array()
  assert_eq(flt[0].to_string(), "X = 3.5")
  let idiv = p.solve([x.is_(compound("//", [int(7), int(2)]))]).to_array()
  assert_eq(idiv[0].to_string(), "X = 3")
  let flr = p.solve([x.is_(compound("div", [int(-7), int(2)]))]).to_array()
  assert_eq(flr[0].to_string(), "X = -4")
  let m = p.solve([x.is_(compound("mod", [int(-7), int(2)]))]).to_array()
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
  let bad = p.solve([x.is_(compound("+", [x, int(1)]))]).to_array()
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
    Clause(compound("single_parent", [sx]), compound("parent", [sx, sy]).not_()),
  ])
  let x = variable("X")
  // not: john has a parent -> fails; an unbound atom succeeds
  let n1 = p
    .solve([
      compound("parent", [x, mary]),
      compound("parent", [x, variable("_")]).not_(),
    ])
    .to_array()
  assert_eq(n1.length(), 0)
  let n2 = p
    .solve([compound("parent", [atom("nobody"), variable("_")]).not_()])
    .to_array()
  assert_eq(n2.length(), 1)
  let n3 = p.solve([compound("single_parent", [atom("ann")])]).to_array()
  assert_eq(n3.length(), 1)
  // disjunction
  let d = p.solve([x.eq(atom("a")).or_(x.eq(atom("b")))]).to_array()
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
