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
  match c.head.head_key() {
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
///
/// ```mbt check
/// test {
///   assert_eq(compound("parent", [atom("john")]).head_key(), Some(("parent", 1)))
///   assert_eq(atom("true").head_key(), Some(("true", 0)))
///   assert_true(int(1).head_key() is None)
/// }
/// ```
pub fn Term::head_key(self : Term) -> (String, Int)? {
  match self {
    Atom(name) => Some((name, 0))
    Compound(name, args) => Some((name, args.length()))
    _ => None
  }
}

///|
/// Builds the conjunction `(a, b)`; also available as `a & b`.
pub fn Term::and_(self : Term, b : Term) -> Term {
  Compound(",", [self, b])
}

///|
/// Builds the disjunction `(a ; b)`.
pub fn Term::or_(self : Term, b : Term) -> Term {
  Compound(";", [self, b])
}

///|
/// Builds the goal `self = other` (unification).
pub fn Term::eq(self : Term, other : Term) -> Term {
  Compound("=", [self, other])
}

///|
/// Builds the goal `self \= other` (non-unifiability).
pub fn Term::neq(self : Term, other : Term) -> Term {
  Compound("\\=", [self, other])
}

///|
/// Builds the goal `self == other` (identical terms).
pub fn Term::identical(self : Term, other : Term) -> Term {
  Compound("==", [self, other])
}

///|
/// Builds the goal `self \== other`.
pub fn Term::not_identical(self : Term, other : Term) -> Term {
  Compound("\\==", [self, other])
}

///|
/// Builds the goal `self is expr` (arithmetic evaluation).
pub fn Term::is_(self : Term, expr : Term) -> Term {
  Compound("is", [self, expr])
}

///|
/// Builds the goal `not(self)`.
pub fn Term::not_(self : Term) -> Term {
  Compound("not", [self])
}
