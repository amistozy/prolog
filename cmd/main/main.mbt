///|
/// Demo: a small family database plus list programming, evaluated by the
/// Prolog EDSL.
///
/// Run with `moon run cmd/main`.
using @prolog {
  atom,
  compound,
  fact,
  rule,
  variable,
  and_,
  program,
  list,
  int,
  stdlib,
}

///|
fn main {
  println("== family ==")
  let john = atom("john")
  let mary = atom("mary")
  let jane = atom("jane")
  let bob = atom("bob")
  // a rule's head and body must share the same variable values
  let rx = variable("X")
  let ry = variable("Y")
  let rz = variable("Z")
  let prog = try! program([
    fact(compound("parent", [john, mary])),
    fact(compound("parent", [john, jane])),
    fact(compound("parent", [mary, bob])),
    // ancestor(X, Y) :- parent(X, Y).
    rule(compound("ancestor", [rx, ry]), compound("parent", [rx, ry])),
    // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    rule(
      compound("ancestor", [rx, ry]),
      and_(compound("parent", [rx, rz]), compound("ancestor", [rz, ry])),
    ),
  ])
  let x = variable("X")
  for ans in prog.solve([compound("parent", [x, variable("_")])]) {
    println(ans)
  }
  let y = variable("Y")
  println("ancestors of bob:")
  for ans in prog.solve([compound("ancestor", [y, bob])]) {
    println(ans)
  }

  println("== lists ==")
  let lib = stdlib()
  let elem = variable("E")
  for
    ans in lib.solve([
      compound("member", [elem, list([int(1), int(2), int(3)])]),
    ]) {
    println(ans)
  }
  let xs = variable("XS")
  for
    ans in lib.solve([
      compound("append", [list([int(1), int(2)]), list([int(3), int(4)]), xs]),
    ]) {
    println(ans)
  }
  let rev = variable("R")
  for
    ans in lib.solve([
      compound("reverse", [list([int(1), int(2), int(3)]), rev]),
    ]) {
    println(ans)
  }
  let n = variable("N")
  for ans in lib.solve([compound("length", [list([atom("a"), atom("b")]), n])]) {
    println(ans)
  }
}
