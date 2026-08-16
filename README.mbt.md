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
  let p = Program([
    Clause::fact(compound("parent", [atom("john"), atom("mary")])),
    Clause::fact(compound("parent", [atom("john"), atom("jane")])),
    Clause::fact(compound("parent", [atom("mary"), atom("bob")])),
  ])

  // 2. query it with logic variables
  let x = variable("X")
  let answers = p.solve([compound("parent", [x, variable("_")])]).to_array()
  assert_eq(answers.length(), 3)
  assert_eq(answers[0].to_string(), "X = john")
  assert_eq(answers[1].to_string(), "X = john")
  assert_eq(answers[2].to_string(), "X = mary")

  // 3. or enumerate lazily
  let first = p.solve_first([compound("parent", [x, variable("_")])])
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
  program,
  solve_first,
  type PrologError,
}
```

## Terms

```mbt check
///|
test {
  // Term("...") parses Prolog syntax directly
  assert_eq(Term("parent(john, X)").to_string(), "parent(john, X)")
  assert_eq(Term("[1, 2 | T]").to_string(), "[1, 2 | T]")
  let x = variable("X")
  assert_eq(x.to_string(), "X")
  assert_eq(atom("john").to_string(), "john")
  assert_eq(int(42).to_string(), "42")
  assert_eq(float(1.5).to_string(), "1.5")
  assert_eq(empty_list().to_string(), "[]")
  assert_eq(list([int(1), int(2)]).to_string(), "[1, 2]")
  assert_eq(cons(int(1), variable("T")).to_string(), "[1 | T]")
  assert_eq(compound("f", [x, int(1)]).to_string(), "f(X, 1)")
  // operator sugar: `|` is disjunction `;`, `&` is conjunction `,`,
  // `+ - * / %` build arithmetic terms, `-x` unary negation
  assert_eq(cons(int(1), cons(int(2), empty_list())).to_string(), "[1, 2]")
  assert_eq((x & atom("true")).to_string(), "X, true")
  assert_eq((x | atom("true")).to_string(), "(X; true)")
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
  let p = Program([
    Clause::fact(compound("parent", [atom("john"), atom("mary")])),
    Clause::fact(compound("parent", [atom("mary"), atom("bob")])),
    // ancestor(X, Y) :- parent(X, Y).
    Clause(compound("ancestor", [x, y]), compound("parent", [x, y])),
    // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    Clause(
      compound("ancestor", [x, y]),
      compound("parent", [x, z]) & compound("ancestor", [z, y]),
    ),
  ])
  let y2 = variable("Y")
  let answers = p.solve([compound("ancestor", [atom("john"), y2])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "Y = mary")
  assert_eq(answers[1].to_string(), "Y = bob")
}
```

Lists can be built either as `list([...])` or as cons chains (`cons`,
`list_tail`); both representations unify with each other. The `|` operator
is reserved for the Prolog disjunction `;`.

## Querying

- `program.solve(goals)` / [`Program::solve`] — a lazy iterator of
  [`Answer`]s
- `program.solve_first(goals)` — the first answer, if any
- `program.solve_all(goals)` — all answers (careful with infinite programs)

An [`Answer`] reports the bindings of the query's named variables, rendered
as `X = john, Y = mary`.

```mbt check
///|
test {
  let p = Program([
    Clause::fact(compound("parent", [atom("john"), atom("mary")])),
    Clause::fact(compound("parent", [atom("mary"), atom("bob")])),
  ])
  let x = variable("X")
  let y = variable("Y")
  let answers = p.solve([compound("parent", [x, y])]).to_array()
  assert_eq(answers.length(), 2)
  assert_eq(answers[0].to_string(), "X = john, Y = mary")
  assert_eq(answers[1].to_string(), "X = mary, Y = bob")
}
```

## Writing programs in Prolog syntax

Instead of (or alongside) the builder API, the package can parse plain Prolog
source text:

```mbt check
///|
test {
  let src =
    #|parent(john, mary). parent(john, jane). parent(mary, bob).
    #|ancestor(X, Y) :- parent(X, Y).
    #|ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    #|
  let p = parse_program(src)
  let y = variable("Y")
  let answers = p.solve([compound("ancestor", [atom("john"), y])]).to_array()
  assert_eq(answers.length(), 3)
  assert_eq(answers[2].to_string(), "Y = bob")
}
```

- `parse_term("parent(john, X)")` — one term (variables with the same name
  share one variable, like in Prolog)
- `parse_clause("ancestor(X, Y) :- parent(X, Y).")` — one clause
- `parse_program(src)` — a whole program (`.`-separated clauses, `%` and
  `/* */` comments)

Supported syntax: variables, atoms (incl. quoted `'...'`), integers, floats
(including `1.5e-2`), base literals (`0x1F`, `0o17`, `0b101`), char codes
(`0'a`, `0'\n`), strings, lists with tails (`[a, b | T]`), compound terms,
`{G}` (DCG goals), DCG rules (`head --> body`), and the usual ISO operators
with their precedences (`:-`, `;`, `,`, `->`, `=`, `is`, `=..`,
`+ - * / // div mod`, `@< ...`, unary `-` and `\+`).

## Builtins and standard library

Builtin predicates (they take precedence over clauses with the same name):

- control: `true`, `fail`, `!` (cut), `,`/`;`/`->` (if-then-else) are
  handled structurally; `(A -> B ; C)` commits to `B` once `A` succeeds
- constraints: `dif/2` (delayed disequality, cf. Scryer's `library(dif)`)
- unification: `=`, `\=`, `==`, `\==`
- arithmetic: `is`, `<`, `>`, `=<`/`<=`, `>=`, `=:=`, `=\=`;
  functors `+ - * / // div mod ^ abs max min sqrt` (with ISO semantics:
  `/` is float division, `//` truncates, `div`/`mod` floor)
- meta: `not/1` and `\+` (with a cut-local scope), `call/N`,
  `ignore/1`, `once/1`, `repeat/0`, `forall/2`, `findall/3`,
  `findall/4` (difference-list tail), `bagof/3`, `setof/3` (with `^`
  existential quantification), `copy_term/2`, `term_variables/2`,
  `numbervars/3` (replaces variables by `'$VAR'(N)`), `subsumes_term/2`
- dynamic predicates: `asserta/1`, `assertz/1`, `retract/1`,
  `retractall/1`, `abolish/1`, `clause/2`, `dynamic/1` (see below)
- term inspection: `functor/3`, `arg/3`, `=../2`, `ground/1`,
  `acyclic_term/1`, `unify_with_occurs_check/2`
- term ordering (standard order, cf. Scryer's `TermOrderCategory`):
  `compare/3`, `sort/2`, `msort/2`, `keysort/2`, `@<`, `@>`, `@=<`, `@>=`
- atoms: `atom_length/2`, `atom_concat/3` (enumerates splits),
  `atom_codes/2`, `atom_chars/2`, `sub_atom/5`
- numbers: `number_codes/2`, `number_chars/2`, `atom_number/2`,
  `char_code/2`
- DCG: `phrase/2`, `phrase/3` (grammar rules are expanded at parse time,
  see below)
- type tests: `var`, `nonvar`, `atom`, `integer`, `float`, `number`,
  `atomic`, `string`, `compound`, `list`
- output: `write(X)`, `writeln(X)`, `writeq(X)` (quotes atoms),
  `nl/0` (all simplified to `println`)

[`stdlib`] provides classic predicates as ordinary clauses, so they stay fully
relational:

```mbt check
///|
test {
  let lib = Program::stdlib()
  let x = variable("X")
  let answers = lib
    .solve([compound("member", [x, list([int(1), int(2), int(3)])])])
    .to_array()
  assert_eq(answers.length(), 3)
  assert_eq(answers[2].to_string(), "X = 3")
}
```

`member/2`, `append/2`, `append/3`, `length/2`, `reverse/2`, `between/3`,
`nth0/3`, `nth1/3`, `nth0/4`, `nth1/4` (with the rest list), `last/2`,
`sum_list/2`, `max_list/2`, `min_list/2`, `select/3`, `flatten/2`,
`permutation/2` are available in any argument direction, e.g.
`append(A, B, [1, 2])` enumerates all splits.
Also included: `maplist/2..6`, `foldl/4..6` (via `call/N`), `memberchk/2`,
`selectchk/3`, `succ/2`, `plus/3`, `numlist/3`, `prefix/2`, `suffix/2`,
`same_length/2`, `list_to_set/2` (dedup, first occurrence kept),
`transpose/2`, `skipn/3` (all from Scryer's `lists.pl`).

## Dynamic predicates

Following Scryer's dynamic clause store, a program can grow and shrink at
runtime:

```mbt check
///|
test {
  let p = Program([])
  // assertz on a fresh predicate creates it dynamically
  let _ = p
    .solve([compound("assertz", [parse_term("parent(john, mary)")])])
    .to_array()
  // the fact is visible in a *new* query on the same program value
  let x = variable("X")
  let answers = p.solve([compound("parent", [x, variable("_")])]).to_array()
  assert_eq(answers.length(), 1)
  assert_eq(answers[0].to_string(), "X = john")
  // retract removes the first match; backtracking removes the next
  let y = variable("Y")
  let retracted = p
    .solve([compound("retract", [compound("parent", [y, variable("_")])])])
    .to_array()
  assert_eq(retracted[0].to_string(), "Y = john")
}
```

- `asserta/1` inserts at the front, `assertz/1` appends; both accept a
  fact or a rule `Head :- Body` (use `Term(...)` / `parse_term` to build
  the rule term). The asserted clause is copied: bound variables become
  their values, free variables are renamed to fresh ones.
- `retract/1` retracts the first matching clause; on backtracking it
  retracts the next match. `retractall/1` removes every matching clause
  and always succeeds. `abolish(Name/Arity)` removes a whole dynamic
  predicate.
- `clause(Head, Body)` enumerates the clauses of a dynamic predicate with
  fresh variables (a variable head searches the whole store).
- `dynamic/1` declares a predicate dynamic at runtime — existing static
  clauses are moved into the dynamic store. `:- dynamic(p/1, q/2).`
  directives are honored by `parse_program`.
- Asserting onto an existing *static* predicate fails (Scryer raises a
  permission error; this EDSL reports it as failure), as do `retract/1`,
  `retractall/1`, `abolish/1` and `clause/2` on static predicates.
- Assertions and retractions are global side effects on the `Program`
  value: they persist across queries and are **not** undone on
  backtracking. A retracted clause is never used again, even by choice
  points created before the retraction.

## Definite clause grammars (DCGs)

Grammar rules are expanded into ordinary clauses at parse time, following
Scryer's `library(dcgs)`: `Head --> Body` becomes
`Head(S0, S) :- Body'(S0, S)`, with `[a, b]` terminals, `(A, B)`
sequencing, `(A ; B)` alternatives, `{G}` plain goals, `!` cuts, `call(G)`
and `phrase(...)` handled as in Scryer. Run a grammar with `phrase/2` or
`phrase/3`:

```mbt check
///|
test {
  let src =
    #|as --> [].
    #|as --> [a], as.
    #|
  let p = parse_program(src)
  let l = variable("L")
  let answers = p
    .solve([compound("phrase", [atom("as"), l])])
    .take(3)
    .to_array()
  assert_eq(answers[0].to_string(), "L = []")
  assert_eq(answers[1].to_string(), "L = [a]")
  assert_eq(answers[2].to_string(), "L = [a, a]")
}
```

The same expansion is available programmatically: [`dcg_rule`] builds a
clause from a grammar rule, [`Term::dcg_body`] expands a grammar body
against two list arguments.

## `dif/2` disequality constraints

`dif(X, Y)` succeeds when `X` and `Y` can be shown to be different and fails
when they are identical; when the terms are not yet comparable the
constraint is delayed and re-checked after every binding, so `X = b` fails
after `dif(X, b)`. Constraints are undone on backtracking, and `\=/2`
keeps its ISO "not unifiable" meaning.

## Laziness

Solutions are produced lazily, so infinite programs can be explored with
`take`:

```mbt check
///|
test {
  let n = variable("N")
  let p = Program([
    Clause::fact(compound("nat", [int(0)])),
    Clause(compound("nat", [compound("s", [n])]), compound("nat", [n])),
  ])
  let x = variable("X")
  let first3 = p.solve([compound("nat", [x])]).take(3).to_array()
  assert_eq(first3[2].to_string(), "X = s(s(0))")
}
```

## Semantics notes

- `Subst` (the substitution passed to `unify`/`deref`/`resolve`) is a
  persistent, immutable hash map (`moonbitlang/core/immut/hashmap`): binding
  a variable returns a new substitution and never mutates the old one, so
  sharing a substitution across branches is always safe.
- Unification performs the occur check and treats numbers numerically
  (`1 = 1.0` succeeds).
- `dif/2` constraints are re-checked after every binding; they are
  snapshotted and undone together with the choice points.
- Dynamic predicates are the one deliberate exception to the pure,
  immutable style: the clause store lives in a `Ref` inside `Program`, so
  every query on the same program value shares it (see the dynamic
  predicates section).
- Undefined predicates simply fail (no error), like many small Prologs.
- `solve_all` on a program with infinitely many answers will not terminate;
  use `solve` with `take`/`next` instead.
- Terms with unknown arity/name render plainly; atoms with special characters
  are not quoted (use [`Term::quoted`](index.html#quoted) / `writeq/1` for a
  round-trippable rendering); integral floats render with a trailing `.0` so
  they round-trip as floats.
