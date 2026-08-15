///|
/// # prolog — a Prolog EDSL in MoonBit
///
/// An embedded logic-programming DSL: build Prolog terms, clauses and
/// programs as ordinary MoonBit values, then run SLD resolution with
/// backtracking to enumerate answers.
///
/// The design follows Scryer Prolog's `Term` representation and conjunction
/// handling (see `reference/scryer-prolog/src/machine/lib_machine/mod.rs`).
///
/// ## Terms
///
/// ```mbt check
/// test {
///   // variables, atoms, integers, lists, compounds
///   let x = variable("X")
///   let t = Compound("parent", [x, atom("john"), list([int(1), int(2)])])
///   assert_eq(t.to_string(), "parent(X, john, [1, 2])")
///   // operators: `|` is list cons, `&` is conjunction, arithmetic builds terms
///   assert_eq((int(1) | cons(int(2), cons(int(3), empty_list()))).to_string(), "[1, 2, 3]")
///   assert_eq((x & atom("true")).to_string(), "X, true")
///   assert_eq((x + int(1)).to_string(), "(X + 1)")
/// }
/// ```
///
/// ## A small program
///
/// ```mbt check
/// test {
///   // a rule's head and body must share the same variable values
///   let ax = variable("X")
///   let ay = variable("Y")
///   let az = variable("Z")
///   let p = program(
///     [
///       fact(compound("parent", [atom("john"), atom("mary")])),
///       fact(compound("parent", [atom("john"), atom("jane")])),
///       // ancestor(X, Y) :- parent(X, Y).
///       rule(compound("ancestor", [ax, ay]), compound("parent", [ax, ay])),
///       // ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
///       rule(
///         compound("ancestor", [ax, ay]),
///         and_(
///           compound("parent", [ax, az]),
///           compound("ancestor", [az, ay]),
///         ),
///       ),
///     ],
///   )
///   let qx = variable("X")
///   let answers = p.solve([compound("parent", [qx, variable("_")])]).to_array()
///   assert_eq(answers.length(), 2)
///   assert_eq(answers[0].to_string(), "X = john")
///   assert_eq(answers[1].to_string(), "X = john")
/// }
/// ```
///
/// ## Key APIs
///
/// - terms: [`variable`], [`atom`], [`int`], [`list`], [`compound`], [`cons`],
///   [`list_tail`], [`empty_list`]
/// - clauses: [`fact`], [`rule`], [`program`]
/// - queries: [`solve`], [`solve_first`], [`solve_all`], [`Answer`]
/// - library predicates: [`stdlib`]
