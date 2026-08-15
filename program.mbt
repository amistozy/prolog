///|
/// A Prolog clause: `head :- body`.
///
/// - [`fact`] builds a clause with body `true`
/// - [`rule`] builds `head :- body`, where `body` is a single goal (use
///   [`and_`] / the `&` operator to build conjunctions)
pub struct Clause {
  head : Term
  body : Term
} derive(Debug)

///|
/// A fact `head.`
pub fn fact(head : Term) -> Clause {
  { head, body: Atom("true") }
}

///|
/// A rule `head :- body`.
pub fn rule(head : Term, body : Term) -> Clause {
  { head, body }
}

///|
/// Errors raised while building a [`Program`].
pub(all) suberror PrologError {
  /// The head of a clause is not a callable term (an atom or a compound).
  InvalidHead(term~ : Term)
} derive(Debug)

///|
/// A logic program: a set of clauses indexed by predicate key
/// (functor name, arity).
///
/// Build one with [`program`] and run queries with [`solve`] or
/// [`Program::solve`].
pub struct Program {
  clauses : Map[(String, Int), Array[Clause]]
} derive(Debug)

///|
/// Builds a program from clauses, e.g.
///
/// ```mbt check
/// test {
///   let x = variable("X")
///   let y = variable("Y")
///   let p = program([
///     fact(compound("parent", [atom("john"), atom("mary")])),
///     // ancestor(X, Y) :- parent(X, Y).
///     rule(compound("ancestor", [x, y]), compound("parent", [x, y])),
///   ])
///   let qx = variable("X")
///   let answers = p.solve([compound("parent", [qx, variable("_")])]).to_array()
///   assert_eq(answers.length(), 1)
///   assert_eq(answers[0].to_string(), "X = john")
/// }
/// ```
pub fn program(clauses : Array[Clause]) -> Program raise PrologError {
  let p = { clauses: Map([]) }
  for c in clauses {
    p.add(c)
  }
  p
}

///|
/// Adds a clause to the program. Raises [`PrologError::InvalidHead`] when
/// the head is not an atom or a compound term.
pub fn Program::add(self : Program, c : Clause) -> Unit raise PrologError {
  match head_key(c.head) {
    Some(key) =>
      match self.clauses.get(key) {
        Some(existing) => existing.push(c)
        None => self.clauses[key] = [c]
      }
    None => raise PrologError::InvalidHead(term=c.head)
  }
}

///|
/// The predicate key of a callable term: `(name, arity)`.
pub fn head_key(t : Term) -> (String, Int)? {
  match t {
    Atom(name) => Some((name, 0))
    Compound(name, args) => Some((name, args.length()))
    _ => None
  }
}

///|
/// Builds the conjunction `(a, b)`; also available as `a & b`.
pub fn and_(a : Term, b : Term) -> Term {
  Compound(",", [a, b])
}

///|
/// Builds the disjunction `(a ; b)`.
pub fn or_(a : Term, b : Term) -> Term {
  Compound(";", [a, b])
}

///|
/// Builds the goal `a = b` (unification).
pub fn eq(a : Term, b : Term) -> Term {
  Compound("=", [a, b])
}

///|
/// Builds the goal `a \= b` (non-unifiability).
pub fn neq(a : Term, b : Term) -> Term {
  Compound("\\=", [a, b])
}

///|
/// Builds the goal `a == b` (identical terms).
pub fn identical(a : Term, b : Term) -> Term {
  Compound("==", [a, b])
}

///|
/// Builds the goal `a \== b`.
pub fn not_identical(a : Term, b : Term) -> Term {
  Compound("\\==", [a, b])
}

///|
/// Builds the goal `x is expr` (arithmetic evaluation).
pub fn is_(x : Term, expr : Term) -> Term {
  Compound("is", [x, expr])
}

///|
/// Builds the goal `not(g)`.
pub fn not_(g : Term) -> Term {
  Compound("not", [g])
}
