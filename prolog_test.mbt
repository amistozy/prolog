///|
/// Black-box tests exercising the public API of the Prolog EDSL.
/// Run with `moon test`.

///|
test "term construction and rendering" {
  let x = @prolog.variable("X")
  assert_eq(x.to_string(), "X")
  assert_eq(@prolog.atom("john").to_string(), "john")
  assert_eq(@prolog.int(42).to_string(), "42")
  assert_eq(@prolog.float(1.5).to_string(), "1.5")
  assert_eq(@prolog.str("hi").to_string(), "\"hi\"")
  assert_eq(@prolog.empty_list().to_string(), "[]")
  assert_eq(@prolog.list([]).to_string(), "[]")
  assert_eq(
    @prolog.list([@prolog.int(1), @prolog.int(2)]).to_string(),
    "[1, 2]",
  )
  assert_eq(@prolog.cons(@prolog.int(1), x).to_string(), "[1 | X]")
  assert_eq(
    @prolog.list_tail([@prolog.int(1), @prolog.int(2)], x).to_string(),
    "[1, 2 | X]",
  )
  assert_eq(
    @prolog.compound("parent", [@prolog.atom("john"), @prolog.atom("mary")]).to_string(),
    "parent(john, mary)",
  )
  // operators: `|` cons (right-nest for chains), `&` conjunction, arithmetic terms
  assert_eq(
    (@prolog.int(1) |
    @prolog.cons(
      @prolog.int(2),
      @prolog.cons(@prolog.int(3), @prolog.empty_list()),
    )).to_string(),
    "[1, 2, 3]",
  )
  assert_eq((x & @prolog.atom("true")).to_string(), "X, true")
  assert_eq((x + @prolog.int(1)).to_string(), "(X + 1)")
  assert_eq((x - @prolog.int(1)).to_string(), "(X - 1)")
  assert_eq((x * @prolog.int(2)).to_string(), "(X * 2)")
  assert_eq((x / @prolog.int(2)).to_string(), "(X / 2)")
  assert_eq((-x).to_string(), "-X")
}

///|
test "family database: multiple solutions and conjunction" {
  let john = @prolog.atom("john")
  let mary = @prolog.atom("mary")
  let jane = @prolog.atom("jane")
  let bob = @prolog.atom("bob")
  let p = try! @prolog.program([
    @prolog.fact(@prolog.compound("parent", [john, mary])),
    @prolog.fact(@prolog.compound("parent", [john, jane])),
    @prolog.fact(@prolog.compound("parent", [mary, bob])),
  ])
  // all children of john
  let x = @prolog.variable("X")
  let answers = @prolog.solve(p, [@prolog.compound("parent", [john, x])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "X = mary")
  assert_eq(answers[1].to_string(), "X = jane")
  // conjunction: X is a parent of Y and Y is bob
  let y = @prolog.variable("Y")
  let conjoined = @prolog.solve(p, [
    @prolog.compound("parent", [x, y]),
    @prolog.eq(y, bob),
  ]).to_array()
  assert_eq(conjoined.length(), 1)
  assert_eq(conjoined[0].to_string(), "X = mary, Y = bob")
  // solve_first
  let first = @prolog.solve_first(p, [@prolog.compound("parent", [john, x])])
  assert_eq(first.unwrap().to_string(), "X = mary")
}

///|
test "recursive rules: ancestor" {
  let john = @prolog.atom("john")
  let mary = @prolog.atom("mary")
  let bob = @prolog.atom("bob")
  // NOTE: head and body must share the same variable values.
  let ax = @prolog.variable("X")
  let ay = @prolog.variable("Y")
  let az = @prolog.variable("Z")
  let p = try! @prolog.program([
    @prolog.fact(@prolog.compound("parent", [john, mary])),
    @prolog.fact(@prolog.compound("parent", [mary, bob])),
    // ancestor(X, Y) :- parent(X, Y).
    @prolog.rule(
      @prolog.compound("ancestor", [ax, ay]),
      @prolog.compound("parent", [ax, ay]),
    ),
    // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    @prolog.rule(
      @prolog.compound("ancestor", [ax, ay]),
      @prolog.and_(
        @prolog.compound("parent", [ax, az]),
        @prolog.compound("ancestor", [az, ay]),
      ),
    ),
  ])
  let y2 = @prolog.variable("Y")
  let answers = @prolog.solve(p, [@prolog.compound("ancestor", [john, y2])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "Y = mary")
  assert_eq(answers[1].to_string(), "Y = bob")
  // standardize apart: same query twice gives same results
  let again = @prolog.solve(p, [@prolog.compound("ancestor", [john, y2])]).to_array()
  assert_eq(again.length(), 2)
}

///|
test "stdlib: member and append in several directions" {
  let lib = @prolog.stdlib()
  let x = @prolog.variable("X")
  // member enumerates
  let m = @prolog.solve(lib, [
    @prolog.compound("member", [
      x,
      @prolog.list([@prolog.int(1), @prolog.int(2), @prolog.int(3)]),
    ]),
  ]).to_array()
  assert_eq(m.length(), 3)
  assert_eq(m[0].to_string(), "X = 1")
  assert_eq(m[1].to_string(), "X = 2")
  assert_eq(m[2].to_string(), "X = 3")
  // member with a ground element
  let found = @prolog.solve(lib, [
    @prolog.compound("member", [
      @prolog.int(2),
      @prolog.list([@prolog.int(1), @prolog.int(2)]),
    ]),
  ]).to_array()
  assert_eq(found.length(), 1)
  // member of an empty list fails
  let none = @prolog.solve(lib, [
    @prolog.compound("member", [x, @prolog.empty_list()]),
  ]).to_array()
  assert_eq(none.length(), 0)
  // append, all three directions
  let a = @prolog.variable("A")
  let b = @prolog.variable("B")
  let c = @prolog.variable("C")
  let ap1 = @prolog.solve(lib, [
    @prolog.compound("append", [
      @prolog.list([@prolog.int(1)]),
      @prolog.list([@prolog.int(2)]),
      c,
    ]),
  ]).to_array()
  assert_eq(ap1.length(), 1)
  assert_eq(ap1[0].to_string(), "C = [1, 2]")
  let ap2 = @prolog.solve(lib, [
    @prolog.compound("append", [
      a,
      b,
      @prolog.list([@prolog.int(1), @prolog.int(2)]),
    ]),
  ]).to_array()
  assert_eq(ap2.length(), 3)
  assert_eq(ap2[0].to_string(), "A = [], B = [1, 2]")
  assert_eq(ap2[1].to_string(), "A = [1], B = [2]")
  assert_eq(ap2[2].to_string(), "A = [1, 2], B = []")
  // append with a partial first argument
  let t = @prolog.variable("T")
  let ap3 = @prolog.solve(lib, [
    @prolog.compound("append", [
      @prolog.cons(@prolog.int(1), t),
      @prolog.list([@prolog.int(2)]),
      @prolog.list([@prolog.int(1), @prolog.int(2)]),
    ]),
  ]).to_array()
  assert_eq(ap3.length(), 1)
  assert_eq(ap3[0].to_string(), "T = []")
}

///|
test "stdlib: length, reverse, between" {
  let lib = @prolog.stdlib()
  let n = @prolog.variable("N")
  let len = @prolog.solve(lib, [
    @prolog.compound("length", [
      @prolog.list([@prolog.atom("a"), @prolog.atom("b")]),
      n,
    ]),
  ]).to_array()
  assert_eq(len.length(), 1)
  assert_eq(len[0].to_string(), "N = 2")
  // length generates lists; length(L, 2) has exactly one solution
  let l = @prolog.variable("L")
  let gen = @prolog.solve(lib, [@prolog.compound("length", [l, @prolog.int(2)])])
    .take(1)
    .to_array()
  assert_eq(gen.length(), 1)
  assert_eq(gen[0].to_string(), "L = [_, _]")
  // reverse
  let r = @prolog.variable("R")
  let rev = @prolog.solve(lib, [
    @prolog.compound("reverse", [
      @prolog.list([@prolog.int(1), @prolog.int(2), @prolog.int(3)]),
      r,
    ]),
  ]).to_array()
  assert_eq(rev.length(), 1)
  assert_eq(rev[0].to_string(), "R = [3, 2, 1]")
  // between
  let x = @prolog.variable("X")
  let bt = @prolog.solve(lib, [
    @prolog.compound("between", [@prolog.int(1), @prolog.int(3), x]),
  ]).to_array()
  assert_eq(bt.length(), 3)
  assert_eq(bt[0].to_string(), "X = 1")
  assert_eq(bt[1].to_string(), "X = 2")
  assert_eq(bt[2].to_string(), "X = 3")
  let empty = @prolog.solve(lib, [
    @prolog.compound("between", [@prolog.int(3), @prolog.int(1), x]),
  ]).to_array()
  assert_eq(empty.length(), 0)
}

///|
test "arithmetic: is and comparisons" {
  let p = try! @prolog.program([])
  let x = @prolog.variable("X")
  let eval = @prolog.solve(p, [
    @prolog.is_(
      x,
      @prolog.compound("*", [
        @prolog.compound("+", [@prolog.int(2), @prolog.int(3)]),
        @prolog.int(4),
      ]),
    ),
  ]).to_array()
  assert_eq(eval.length(), 1)
  assert_eq(eval[0].to_string(), "X = 20")
  let flt = @prolog.solve(p, [
    @prolog.is_(x, @prolog.compound("/", [@prolog.int(7), @prolog.int(2)])),
  ]).to_array()
  assert_eq(flt[0].to_string(), "X = 3.5")
  let idiv = @prolog.solve(p, [
    @prolog.is_(x, @prolog.compound("//", [@prolog.int(7), @prolog.int(2)])),
  ]).to_array()
  assert_eq(idiv[0].to_string(), "X = 3")
  let flr = @prolog.solve(p, [
    @prolog.is_(x, @prolog.compound("div", [@prolog.int(-7), @prolog.int(2)])),
  ]).to_array()
  assert_eq(flr[0].to_string(), "X = -4")
  let m = @prolog.solve(p, [
    @prolog.is_(x, @prolog.compound("mod", [@prolog.int(-7), @prolog.int(2)])),
  ]).to_array()
  assert_eq(m[0].to_string(), "X = 1")
  let neg = @prolog.solve(p, [@prolog.is_(x, -@prolog.int(5))]).to_array()
  assert_eq(neg[0].to_string(), "X = -5")
  // comparisons
  let lt = @prolog.solve(p, [
    @prolog.compound("<", [@prolog.int(1), @prolog.int(2)]),
  ]).to_array()
  assert_eq(lt.length(), 1)
  let le = @prolog.solve(p, [
    @prolog.compound("=<", [@prolog.int(2), @prolog.int(2)]),
  ]).to_array()
  assert_eq(le.length(), 1)
  let gt = @prolog.solve(p, [
    @prolog.compound(">", [@prolog.int(1), @prolog.int(2)]),
  ]).to_array()
  assert_eq(gt.length(), 0)
  // is fails on unbound arithmetic
  let bad = @prolog.solve(p, [
    @prolog.is_(x, @prolog.compound("+", [x, @prolog.int(1)])),
  ]).to_array()
  assert_eq(bad.length(), 0)
}

///|
test "unification builtins: equal, neq, identical, not identical" {
  let p = try! @prolog.program([])
  let x = @prolog.variable("X")
  let y = @prolog.variable("Y")
  let eq1 = @prolog.solve(p, [@prolog.eq(x, @prolog.atom("a"))]).to_array()
  assert_eq(eq1.length(), 1)
  assert_eq(eq1[0].to_string(), "X = a")
  let eq2 = @prolog.solve(p, [@prolog.eq(x, y)]).to_array()
  assert_eq(eq2[0].to_string(), "X = Y")
  let eq3 = @prolog.solve(p, [@prolog.eq(@prolog.int(1), @prolog.float(1.0))]).to_array()
  assert_eq(eq3.length(), 1)
  let neq = @prolog.solve(p, [@prolog.neq(@prolog.atom("a"), @prolog.atom("b"))]).to_array()
  assert_eq(neq.length(), 1)
  let neq2 = @prolog.solve(p, [@prolog.neq(x, @prolog.atom("b"))]).to_array()
  assert_eq(neq2.length(), 0)
  let ident = @prolog.solve(p, [@prolog.identical(x, x)]).to_array()
  assert_eq(ident.length(), 1)
  let ident2 = @prolog.solve(p, [@prolog.identical(x, y)]).to_array()
  assert_eq(ident2.length(), 0)
  let nident = @prolog.solve(p, [@prolog.not_identical(x, y)]).to_array()
  assert_eq(nident.length(), 1)
  // \= after binding
  let bound = @prolog.solve(p, [
    @prolog.eq(x, @prolog.atom("a")),
    @prolog.neq(x, @prolog.atom("b")),
  ]).to_array()
  assert_eq(bound.length(), 1)
}

///|
test "negation, disjunction, cut" {
  let john = @prolog.atom("john")
  let mary = @prolog.atom("mary")
  let sx = @prolog.variable("X")
  let sy = @prolog.variable("Y")
  let p = try! @prolog.program([
    @prolog.fact(@prolog.compound("parent", [john, mary])),
    @prolog.rule(
      @prolog.compound("single_parent", [sx]),
      @prolog.not_(@prolog.compound("parent", [sx, sy])),
    ),
  ])
  let x = @prolog.variable("X")
  // not: john has a parent -> fails; an unbound atom succeeds
  let n1 = @prolog.solve(p, [
    @prolog.compound("parent", [x, mary]),
    @prolog.not_(@prolog.compound("parent", [x, @prolog.variable("_")])),
  ]).to_array()
  assert_eq(n1.length(), 0)
  let n2 = @prolog.solve(p, [
    @prolog.not_(
      @prolog.compound("parent", [@prolog.atom("nobody"), @prolog.variable("_")]),
    ),
  ]).to_array()
  assert_eq(n2.length(), 1)
  let n3 = @prolog.solve(p, [
    @prolog.compound("single_parent", [@prolog.atom("ann")]),
  ]).to_array()
  assert_eq(n3.length(), 1)
  // disjunction
  let d = @prolog.solve(p, [
    @prolog.or_(
      @prolog.eq(x, @prolog.atom("a")),
      @prolog.eq(x, @prolog.atom("b")),
    ),
  ]).to_array()
  assert_eq(d.length(), 2)
  assert_eq(d[0].to_string(), "X = a")
  assert_eq(d[1].to_string(), "X = b")
  // cut: keep only the first solution of a predicate
  let p2 = try! @prolog.program([
    @prolog.fact(@prolog.compound("choice", [@prolog.int(1)])),
    @prolog.fact(@prolog.compound("choice", [@prolog.int(2)])),
    @prolog.fact(@prolog.compound("choice", [@prolog.int(3)])),
  ])
  let y = @prolog.variable("Y")
  let all = @prolog.solve(p2, [@prolog.compound("choice", [y])]).to_array()
  assert_eq(all.length(), 3)
  let cut = @prolog.solve(p2, [
    @prolog.compound("choice", [y]),
    @prolog.atom("!"),
  ]).to_array()
  assert_eq(cut.length(), 1)
  assert_eq(cut[0].to_string(), "Y = 1")
}

///|
test "lazy solutions with an infinite program" {
  // natural numbers: nat(0). nat(s(N)) :- nat(N).
  let n = @prolog.variable("N")
  let p = try! @prolog.program([
    @prolog.fact(@prolog.compound("nat", [@prolog.int(0)])),
    @prolog.rule(
      @prolog.compound("nat", [@prolog.compound("s", [n])]),
      @prolog.compound("nat", [n]),
    ),
  ])
  let x = @prolog.variable("X")
  let first3 = @prolog.solve(p, [@prolog.compound("nat", [x])])
    .take(3)
    .to_array()
  assert_eq(first3.length(), 3)
  assert_eq(first3[0].to_string(), "X = 0")
  assert_eq(first3[1].to_string(), "X = s(0)")
  assert_eq(first3[2].to_string(), "X = s(s(0))")
}

///|
test "program validation raises on invalid heads" {
  try @prolog.program([@prolog.fact(@prolog.int(42))]) catch {
    @prolog.PrologError::InvalidHead(term=t) => assert_eq(t.to_string(), "42")
  } noraise {
    _ => fail("expected InvalidHead")
  }
}

///|
test "type tests" {
  let p = try! @prolog.program([])
  let x = @prolog.variable("X")
  let is_var = @prolog.solve(p, [@prolog.compound("var", [x])]).to_array()
  assert_eq(is_var.length(), 1)
  let is_atom = @prolog.solve(p, [@prolog.compound("atom", [@prolog.atom("a")])]).to_array()
  assert_eq(is_atom.length(), 1)
  let is_list = @prolog.solve(p, [
    @prolog.compound("list", [@prolog.empty_list()]),
  ]).to_array()
  assert_eq(is_list.length(), 1)
  let is_compound = @prolog.solve(p, [
    @prolog.compound("compound", [@prolog.compound("f", [@prolog.int(1)])]),
  ]).to_array()
  assert_eq(is_compound.length(), 1)
  let not_list = @prolog.solve(p, [
    @prolog.compound("list", [@prolog.atom("a")]),
  ]).to_array()
  assert_eq(not_list.length(), 0)
}
