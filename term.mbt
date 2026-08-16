///|
/// Prolog variables: a unique `id` plus a display `name`.
///
/// Two occurrences of the *same* `VarRef` value denote the same logic
/// variable. Every call to [`variable`] allocates a brand-new id, so writing
/// `variable("X")` twice produces two *different* variables; share one value
/// through a `let` binding instead:
///
/// ```mbt check
/// test {
///   let x = variable("X")
///   let clause_head = compound("parent", [x, atom("mary")])
///   let clause_body = compound("likes", [x, atom("mary")])
///   assert_eq(clause_head.to_string(), "parent(X, mary)")
///   assert_eq(clause_body.to_string(), "likes(X, mary)")
/// }
/// ```
pub(all) struct VarRef {
  id : Int
  name : String
} derive(Debug)

///|
/// A Prolog term, modeled after Scryer Prolog's `Term` enum
/// (`reference/scryer-prolog/src/machine/lib_machine/mod.rs`).
///
/// - atoms: `Atom("john")` or [`atom`]
/// - variables: `Var(ref)` or [`variable`]
/// - integers: `Int(42)` or [`int`]
/// - floats: `Float(1.5)` or [`float`]
/// - strings: `Str("text")` or [`str`]
/// - proper lists: `List([...])` or [`list`]
/// - compound terms: `Compound("f", [a, b])` or [`compound`]
///
/// Lists are also represented as cons cells `'.'(H, T)` (built by
/// [`cons`] or [`list_tail`]), so `list([1, 2, 3])` and
/// `cons(1, cons(2, cons(3, empty_list())))` unify with each other.
pub enum Term {
  Int(Int)
  Float(Double)
  Atom(String)
  Str(String)
  Var(VarRef)
  List(Array[Term])
  Compound(String, Array[Term])
} derive(Debug)

///|
/// Global counter backing [`variable`]; every call to `var` grabs a fresh id.
let var_counter : Ref[Int] = { val: 0 }

///|
/// Parses a term from Prolog syntax: `Term("parent(john, X)")`,
/// `Term("[1, 2 | T]")`, `Term("X is 2 * 3")`. Variables with the same name
/// share one variable, like in Prolog source text.
///
/// ```mbt check
/// test {
///   inspect(
///     @prolog.Term("parent(john, X)").to_string(),
///     content="parent(john, X)",
///   )
///   inspect(@prolog.Term("[1, 2]").to_string(), content="[1, 2]")
///   inspect(@prolog.Term("X + 1").to_string(), content="(X + 1)")
/// }
/// ```
pub fn Term::Term(text : String) -> Term raise ParseError {
  parse_term(text)
}

///|
/// Allocates a fresh logic variable with the given display `name`.
///
/// ```mbt check
/// test {
///   let a = variable("X")
///   let b = variable("X")
///   let a_ref = match a {
///     Term::Var(x) => x
///     _ => abort("expected a variable")
///   }
///   let b_ref = match b {
///     Term::Var(x) => x
///     _ => abort("expected a variable")
///   }
///   assert_true(a_ref.id != b_ref.id)
///   assert_eq(a_ref.name, "X")
/// }
/// ```
pub fn variable(name : String) -> Term {
  var_counter.val = var_counter.val + 1
  Var({ id: var_counter.val, name })
}

///|
/// An atom, e.g. `atom("john")`.
pub fn atom(name : String) -> Term {
  Atom(name)
}

///|
/// A float, e.g. `float(1.5)`.
pub fn float(d : Double) -> Term {
  Float(d)
}

///|
/// An integer term, e.g. `int(42)` (or the variant `Term::Int(42)`).
pub fn int(i : Int) -> Term {
  Int(i)
}

///|
/// A Prolog string (double-quoted text), e.g. `str("hello")`.
pub fn str(s : String) -> Term {
  Str(s)
}

///|
/// A proper list, e.g. `list([1, 2, 3])` or `list([])`.
pub fn list(elems : Array[Term]) -> Term {
  List(elems)
}

///|
/// A compound term, e.g. `compound("parent", [atom("john"), atom("mary")])`.
pub fn compound(functor : String, args : Array[Term]) -> Term {
  Compound(functor, args)
}

///|
/// The list constructor `[H | T]`; use [`cons`] (or [`list_tail`]) to build
/// lists as cons chains — the `|` operator is reserved for the Prolog
/// disjunction `;`.
pub fn cons(head : Term, tail : Term) -> Term {
  Compound(".", [head, tail])
}

///|
/// A list with a non-empty tail: `[e1, ..., en | tail]`.
pub fn list_tail(elems : Array[Term], tail : Term) -> Term {
  let mut acc = tail
  for i = elems.length() - 1; i >= 0; i = i - 1 {
    acc = Compound(".", [elems[i], acc])
  }
  acc
}

///|
/// The empty list `[]`.
pub fn empty_list() -> Term {
  Atom("[]")
}

///|
/// `a + b` builds the Prolog arithmetic term `+(a, b)`, exactly like
/// writing `a + b` inside a Prolog program.
pub impl Add for Term with fn add(self, other) {
  Compound("+", [self, other])
}

///|
/// `a - b` builds the term `-(a, b)`.
pub impl Sub for Term with fn sub(self, other) {
  Compound("-", [self, other])
}

///|
/// `a * b` builds the term `*(a, b)`.
pub impl Mul for Term with fn mul(self, other) {
  Compound("*", [self, other])
}

///|
/// `a / b` builds the term `/(a, b)` (float division when evaluated).
pub impl Div for Term with fn div(self, other) {
  Compound("/", [self, other])
}

///|
/// `a % b` builds the term `mod(a, b)`.
pub impl Mod for Term with fn mod(self, other) {
  Compound("mod", [self, other])
}

///|
/// Unary `-x` builds the term `-(x)`.
pub impl Neg for Term with fn neg(self) {
  Compound("-", [self])
}

///|
/// `a | b` builds the disjunction `(a ; b)`.
pub impl BitOr for Term with fn lor(self, other) {
  Compound(";", [self, other])
}

///|
/// `a & b` builds the conjunction `(a, b)`.
pub impl BitAnd for Term with fn land(self, other) {
  Compound(",", [self, other])
}

///|
/// Structural equality of terms (`==`), mirroring Prolog's `==/2` on
/// ground terms: identical structure, no unification involved.
pub impl Eq for Term with fn equal(a, b) {
  match (a, b) {
    (Int(x), Int(y)) => x == y
    (Float(x), Float(y)) => x == y
    (Int(x), Float(y)) => x.to_double() == y
    (Float(x), Int(y)) => x == y.to_double()
    (Atom(x), Atom(y)) => x == y
    (Str(x), Str(y)) => x == y
    (Var(x), Var(y)) => x.id == y.id
    (List(xs), List(ys)) =>
      xs.length() == ys.length() &&
      xs
      .zip(ys)
      .all(p => {
        let (a, b) = p
        a == b
      })
    (Compound(f1, a1), Compound(f2, a2)) =>
      f1 == f2 &&
      a1.length() == a2.length() &&
      a1
      .zip(a2)
      .all(p => {
        let (a, b) = p
        a == b
      })
    _ => false
  }
}

///|
/// Renders a term in Prolog syntax: `parent(john, mary)`, `[1, 2 | X]`,
/// `(a, b)`, `(X + 1) * 2`.
pub impl Show for Term with fn to_string(self) {
  match self {
    Int(i) => i.to_string()
    Float(d) => render_float(d)
    Atom(name) => name
    Str(s) => "\"\{s}\""
    Var(v) => if v.name == "" { "_\{v.id}" } else { v.name }
    List(xs) => render_chain(list_tail(xs, Atom("[]")))
    Compound(".", [head, tail]) => render_chain(cons(head, tail))
    Compound(name, args) => render_compound(name, args)
  }
}

///|
/// Renders a float in Prolog syntax. MoonBit's `to_string` drops the
/// decimal point of integral doubles (`4.0` becomes `"4"`), which would
/// round-trip as an *integer*; append `.0` so `4.0` stays a float.
fn render_float(d : Double) -> String {
  let s = d.to_string()
  if s.contains(".") ||
    s.contains("e") ||
    s.contains("E") ||
    s.contains("n") ||
    s.contains("i") {
    s
  } else {
    s + ".0"
  }
}

///|
/// Renders a cons chain as `[a, b]` or `[a, b | tail]`.
fn render_chain(t : Term) -> String {
  let heads : Array[String] = []
  let mut cur = t
  for ;; {
    match cur {
      Compound(".", [h, tail]) => {
        heads.push("\{h}")
        cur = tail
      }
      List(xs) => {
        // A `List` in tail position contributes its elements and ends the
        // chain, e.g. `[1 | [2, 3]]` renders as `[1, 2, 3]`.
        for x in xs {
          heads.push("\{x}")
        }
        cur = Atom("[]")
      }
      _ => break
    }
  }
  let tail_s = if cur is Atom("[]") { "" } else { " | \{cur}" }
  let sep = ", "
  "[\{heads.join(sep)}\{tail_s}]"
}

///|
/// Renders a compound term, with infix notation for arithmetic and
/// `,` / `;` for conjunction / disjunction.
fn render_compound(name : String, args : Array[Term]) -> String {
  if name == "," && args.length() == 2 {
    "\{args[0]}, \{args[1]}"
  } else if name == ";" && args.length() == 2 {
    "(\{args[0]}; \{args[1]})"
  } else if name == "{}" && args.length() == 1 {
    "{ \{args[0]} }"
  } else if args.length() == 2 &&
    (
      name == "+" ||
      name == "-" ||
      name == "*" ||
      name == "/" ||
      name == "//" ||
      name == "div" ||
      name == "mod" ||
      name == "^" ||
      name == "-->"
    ) {
    "(\{args[0]} \{name} \{args[1]})"
  } else if args.length() == 2 &&
    (
      name == "=" ||
      name == "\\=" ||
      name == "==" ||
      name == "\\==" ||
      name == "=:=" ||
      name == "=\\=" ||
      name == "is" ||
      name == "=.." ||
      name == "<" ||
      name == ">" ||
      name == "=<" ||
      name == ">=" ||
      name == "@<" ||
      name == "@>" ||
      name == "@=<" ||
      name == "@>="
    ) {
    "\{args[0]} \{name} \{args[1]}"
  } else if name == "-" && args.length() == 1 {
    "-\{args[0]}"
  } else if name == "\\+" && args.length() == 1 {
    "\\+ \{args[0]}"
  } else {
    "\{name}(\{args.map(x => "\{x}").join(", ")})"
  }
}
