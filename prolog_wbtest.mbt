///|
/// White-box tests: internal helpers of the engine and unification.

///|
test "unify: variables, occurs check, chains" {
  // var-var binds one to the other
  let x = variable("X")
  let y = variable("Y")
  let s = match x.unify(y, @immut_hashmap.HashMap([])) {
    Some(s) => s
    None => abort("x = y should unify")
  }
  assert_true(x.deref(s) is Var(_))
  // occurs check rejects f(X) = X
  let z = variable("Z")
  let cyclic = compound("f", [z]).unify(z, @immut_hashmap.HashMap([]))
  assert_true(cyclic is None)
  // proper list unifies with a cons chain
  let t = variable("T")
  let s2 = match
    list([int(1), int(2)]).unify(
      cons(int(1), cons(int(2), t)),
      @immut_hashmap.HashMap([]),
    ) {
    Some(s2) => s2
    None => abort("list vs chain should unify")
  }
  assert_eq(t.deref(s2).to_string(), "[]")
  // mismatched lengths fail
  let s3 = list([int(1), int(2)]).unify(
    list([int(1)]),
    @immut_hashmap.HashMap([]),
  )
  assert_true(s3 is None)
  // numeric equality: 1 = 1.0
  let s4 = int(1).unify(float(1.0), @immut_hashmap.HashMap([]))
  assert_true(s4 is Some(_))
  // deep structure
  let s5 = compound("f", [compound("g", [x]), int(2)]).unify(
    compound("f", [compound("g", [atom("a")]), int(2)]),
    @immut_hashmap.HashMap([]),
  )
  assert_eq(
    match s5 {
      Some(s) => x.deref(s).to_string()
      None => abort("should unify")
    },
    "a",
  )
}

///|
test "unify: List tail unification" {
  // [1 | T] = [1, 2, 3] binds T to [2, 3]
  let t = variable("T")
  let s = match
    cons(int(1), t).unify(
      list([int(1), int(2), int(3)]),
      @immut_hashmap.HashMap([]),
    ) {
    Some(s) => s
    None => abort("should unify")
  }
  assert_eq(t.deref(s).to_string(), "[2, 3]")
  // [1, 2] = [1 | T] binds T to [2]
  let t2 = variable("T")
  let s2 = match
    list([int(1), int(2)]).unify(cons(int(1), t2), @immut_hashmap.HashMap([])) {
    Some(s2) => s2
    None => abort("should unify")
  }
  assert_eq(t2.deref(s2).to_string(), "[2]")
  // 3-element list vs 1-element chain binds head and tail
  let t3 = variable("T")
  let x3 = variable("X")
  let s3 = match
    list([int(1), int(2), int(3)]).unify(
      cons(x3, t3),
      @immut_hashmap.HashMap([]),
    ) {
    Some(s3) => s3
    None => abort("should unify")
  }
  assert_eq(x3.deref(s3).to_string(), "1")
  assert_eq(t3.deref(s3).to_string(), "[2, 3]")
}

///|
test "list_parts" {
  assert_eq(
    match list_parts(list([int(1), int(2)])) {
      Some((elems, tail)) => "\{elems.length()},\{tail.to_string()}"
      None => abort("expected a list")
    },
    "2,[]",
  )
  assert_eq(
    match list_parts(cons(int(1), cons(int(2), empty_list()))) {
      Some((elems, tail)) => "\{elems.length()},\{tail.to_string()}"
      None => abort("expected a list")
    },
    "2,[]",
  )
  assert_true(list_parts(atom("a")) is None)
  // partial list keeps its tail
  let t = variable("T")
  assert_eq(
    match list_parts(cons(int(1), t)) {
      Some((elems, tail)) => "\{elems.length()},\{tail.to_string()}"
      None => abort("expected a list")
    },
    "1,T",
  )
}

///|
test "eval_arith" {
  assert_eq(
    match
      eval_arith(
        compound("+", [int(1), compound("*", [int(2), int(3)])]),
        @immut_hashmap.HashMap([]),
      ) {
      Some(v) => v.to_string()
      None => abort("expected a value")
    },
    "7",
  )
  assert_true(
    eval_arith(compound("/", [int(1), int(0)]), @immut_hashmap.HashMap([]))
    is None,
  )
  assert_true(eval_arith(variable("X"), @immut_hashmap.HashMap([])) is None)
  assert_eq(
    match
      eval_arith(compound("mod", [int(-7), int(2)]), @immut_hashmap.HashMap([])) {
      Some(v) => v.to_string()
      None => abort("expected a value")
    },
    "1",
  )
}

///|
test "machine: fresh variables per clause invocation" {
  // same clause invoked twice in one query must not share variables
  let t = variable("T")
  let p = Program([
    Clause(compound("twice", [t]), compound("t", [t]).and_(compound("t", [t]))),
    Clause::fact(compound("t", [int(1)])),
    Clause::fact(compound("t", [int(2)])),
  ])
  let x = variable("X")
  let answers = p.solve([compound("twice", [x])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "X = 1")
  assert_eq(answers[1].to_string(), "X = 2")
}

///|
test "machine: cut inside not stays local" {
  let p = Program([
    Clause::fact(compound("p", [int(1)])),
    Clause::fact(compound("p", [int(2)])),
  ])
  let x = variable("X")
  // not((true, !)) fails since (true, !) succeeds -> no answers
  let answers = p
    .solve([compound("p", [x]), atom("true").and_(atom("!")).not_()])
    .to_array()
  assert_eq(answers.length(), 0)
  // not(p(99)) succeeds, and both p solutions survive
  let answers2 = p
    .solve([compound("p", [x]), compound("p", [int(99)]).not_()])
    .to_array()
  assert_eq(answers2.length(), 2)
  assert_eq(answers2[1].to_string(), "X = 2")
}

///|
test "machine: deep recursion does not overflow" {
  // chain of 5000 facts linked by next/2, walk the whole chain
  let clauses : Array[Clause] = []
  for i in 0..<5000 {
    clauses.push(Clause::fact(compound("next", [int(i), int(i + 1)])))
  }
  let p = Program(clauses)
  let x = variable("X")
  let answers = p.solve([compound("next", [int(0), x])]).to_array()
  assert_eq(answers.length(), 1)
  assert_eq(answers[0].to_string(), "X = 1")
}
