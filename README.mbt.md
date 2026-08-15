# amistozy/prolog

A Prolog **EDSL** (embedded domain-specific language) in MoonBit: build Prolog
terms, clauses and programs as ordinary MoonBit values, then run SLD
resolution with backtracking to enumerate answers.

The design is inspired by [Scryer Prolog](https://github.com/mthom/scryer-prolog)
(see `reference/scryer-prolog`): its `Term` representation, right-nested
conjunction `(a, b)`, and answer bindings follow the same shape.

## Quick start

```mbt check
///|
test {
  // 1. build a program from facts and rules
  let p = program([
    fact(compound("parent", [atom("john"), atom("mary")])),
    fact(compound("parent", [atom("john"), atom("jane")])),
    fact(compound("parent", [atom("mary"), atom("bob")])),
  ])

  // 2. query it with logic variables
  let x = variable("X")
  let answers = p.solve([compound("parent", [x, variable("_")])]).to_array()
  assert_eq(answers.length(), 3)
  assert_eq(answers[0].to_string(), "X = john")
  assert_eq(answers[1].to_string(), "X = john")
  assert_eq(answers[2].to_string(), "X = mary")

  // 3. or enumerate lazily
  let first = solve_first(p, [compound("parent", [x, variable("_")])])
  assert_eq(first.unwrap().to_string(), "X = john")
}
```

Consumers of the package can drop the `@prolog.` prefix with a `using`
declaration (types use the `type` keyword):

```mbt nocheck
///|
using @prolog {
  atom,
  compound,
  fact,
  rule,
  variable,
  and_,
  program,
  solve_first,
  type PrologError,
}
```

## Terms

```mbt check
///|
test {
  let x = variable("X")
  assert_eq(x.to_string(), "X")
  assert_eq(atom("john").to_string(), "john")
  assert_eq(int(42).to_string(), "42")
  assert_eq(float(1.5).to_string(), "1.5")
  assert_eq(empty_list().to_string(), "[]")
  assert_eq(list([int(1), int(2)]).to_string(), "[1, 2]")
  assert_eq(cons(int(1), variable("T")).to_string(), "[1 | T]")
  assert_eq(compound("f", [x, int(1)]).to_string(), "f(X, 1)")
  // operator sugar: `|` is list cons, `&` is conjunction,
  // `+ - * / %` build arithmetic terms, `-x` unary negation
  assert_eq((int(1) | cons(int(2), empty_list())).to_string(), "[1, 2]")
  assert_eq((x & atom("true")).to_string(), "X, true")
  assert_eq((x + int(1)).to_string(), "(X + 1)")
}
```

**Important:** every call to `variable(name)` creates a *brand-new* logic
variable. A rule's head and body must share the same variable *values*:

```mbt check
///|
test {
  // X and Y are the same variable in head and body:
  let x = variable("X")
  let y = variable("Y")
  let z = variable("Z")
  let p = program([
    fact(compound("parent", [atom("john"), atom("mary")])),
    fact(compound("parent", [atom("mary"), atom("bob")])),
    // ancestor(X, Y) :- parent(X, Y).
    rule(compound("ancestor", [x, y]), compound("parent", [x, y])),
    // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    rule(
      compound("ancestor", [x, y]),
      and_(compound("parent", [x, z]), compound("ancestor", [z, y])),
    ),
  ])
  let y2 = variable("Y")
  let answers = p.solve([compound("ancestor", [atom("john"), y2])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "Y = mary")
  assert_eq(answers[1].to_string(), "Y = bob")
}
```

Lists can be built either as `list([...])` or as cons chains (`h | t`,
`list_tail`); both representations unify with each other.

## Querying

- `solve(program, goals)` / `Program::solve` — a lazy iterator of [`Answer`]s
- `solve_first(program, goals)` — the first answer, if any
- `solve_all(program, goals)` — all answers (careful with infinite programs)

An [`Answer`] reports the bindings of the query's named variables, rendered
as `X = john, Y = mary`.

```mbt check
///|
test {
  let p = program([
    fact(compound("parent", [atom("john"), atom("mary")])),
    fact(compound("parent", [atom("mary"), atom("bob")])),
  ])
  let x = variable("X")
  let y = variable("Y")
  let answers = p.solve([compound("parent", [x, y])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "X = john, Y = mary")
  assert_eq(answers[1].to_string(), "X = mary, Y = bob")
}
```

## Builtins and standard library

Builtin predicates (they take precedence over clauses with the same name):

- control: `true`, `fail`, `!` (cut), `,`/`;` are handled structurally
- unification: `=`, `\=`, `==`, `\==`
- arithmetic: `is`, `<`, `>`, `=<`/`<=`, `>=`, `=:=`, `=\=`;
  functors `+ - * / // div mod abs` (with ISO semantics: `/` is float
  division, `//` truncates, `div`/`mod` floor)
- meta: `not(G)` (with a cut-local scope), `call(G)`
- type tests: `var`, `nonvar`, `atom`, `integer`, `float`, `number`,
  `atomic`, `string`, `compound`, `list`
- output: `write(X)`, `writeln(X)` (simplified to `println`)

[`stdlib`] provides classic predicates as ordinary clauses, so they stay fully
relational:

```mbt check
///|
test {
  let lib = stdlib()
  let x = variable("X")
  let answers = lib
    .solve([compound("member", [x, list([int(1), int(2), int(3)])])])
    .to_array()
  assert_eq(answers.length(), 3)
  assert_eq(answers[2].to_string(), "X = 3")
}
```

`member/2`, `append/3`, `length/2`, `reverse/2`, `between/3` are available
in any argument direction, e.g. `append(A, B, [1, 2])` enumerates all splits.

## Laziness

Solutions are produced lazily, so infinite programs can be explored with
`take`:

```mbt check
///|
test {
  let n = variable("N")
  let p = program([
    fact(compound("nat", [int(0)])),
    rule(compound("nat", [compound("s", [n])]), compound("nat", [n])),
  ])
  let x = variable("X")
  let first3 = p.solve([compound("nat", [x])]).take(3).to_array()
  assert_eq(first3[2].to_string(), "X = s(s(0))")
}
```

## Semantics notes

- Unification performs the occur check and treats numbers numerically
  (`1 = 1.0` succeeds).
- Undefined predicates simply fail (no error), like many small Prologs.
- `solve_all` on a program with infinitely many answers will not terminate;
  use `solve` with `take`/`next` instead.
- Terms with unknown arity/name render plainly; atoms with special characters
  are not quoted.
