///|
/// Demo: a small family database plus list programming, evaluated by the
/// Prolog EDSL.
///
/// Run with `moon run cmd/main`.
fn main {
  println("== family ==")
  let john = @prolog.atom("john")
  let mary = @prolog.atom("mary")
  let jane = @prolog.atom("jane")
  let bob = @prolog.atom("bob")
  // a rule's head and body must share the same variable values
  let rx = @prolog.variable("X")
  let ry = @prolog.variable("Y")
  let rz = @prolog.variable("Z")
  let prog = try! @prolog.program([
    @prolog.fact(@prolog.compound("parent", [john, mary])),
    @prolog.fact(@prolog.compound("parent", [john, jane])),
    @prolog.fact(@prolog.compound("parent", [mary, bob])),
    // ancestor(X, Y) :- parent(X, Y).
    @prolog.rule(
      @prolog.compound("ancestor", [rx, ry]),
      @prolog.compound("parent", [rx, ry]),
    ),
    // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    @prolog.rule(
      @prolog.compound("ancestor", [rx, ry]),
      @prolog.and_(
        @prolog.compound("parent", [rx, rz]),
        @prolog.compound("ancestor", [rz, ry]),
      ),
    ),
  ])
  let x = @prolog.variable("X")
  for
    ans in prog.solve([@prolog.compound("parent", [x, @prolog.variable("_")])]) {
    println(ans)
  }
  let y = @prolog.variable("Y")
  println("ancestors of bob:")
  for ans in prog.solve([@prolog.compound("ancestor", [y, bob])]) {
    println(ans)
  }

  println("== lists ==")
  let lib = @prolog.stdlib()
  let elem = @prolog.variable("E")
  for
    ans in lib.solve([
      @prolog.compound("member", [
        elem,
        @prolog.list([@prolog.int(1), @prolog.int(2), @prolog.int(3)]),
      ]),
    ]) {
    println(ans)
  }
  let xs = @prolog.variable("XS")
  for
    ans in lib.solve([
      @prolog.compound("append", [
        @prolog.list([@prolog.int(1), @prolog.int(2)]),
        @prolog.list([@prolog.int(3), @prolog.int(4)]),
        xs,
      ]),
    ]) {
    println(ans)
  }
  let rev = @prolog.variable("R")
  for
    ans in lib.solve([
      @prolog.compound("reverse", [
        @prolog.list([@prolog.int(1), @prolog.int(2), @prolog.int(3)]),
        rev,
      ]),
    ]) {
    println(ans)
  }
  let n = @prolog.variable("N")
  for
    ans in lib.solve([
      @prolog.compound("length", [
        @prolog.list([@prolog.atom("a"), @prolog.atom("b")]),
        n,
      ]),
    ]) {
    println(ans)
  }
}
