///|
/// Definite clause grammars (DCGs), following Scryer Prolog's
/// `library(dcgs)` design (`reference/scryer-prolog/src/lib/dcgs.pl`).
///
/// A grammar rule `Head --> Body` is expanded at clause-construction time
/// into an ordinary clause `Head(S0, S) :- Body'(S0, S)`, where the body is
/// translated with two extra list arguments:
///
/// - `[a, b]` (a terminal list) becomes `S0 = [a, b | S]`
/// - `(A, B)` becomes `A'(S0, S1), B'(S1, S)`
/// - `(A ; B)` becomes a disjunction of the expanded branches
/// - `{G}` (a plain Prolog goal) becomes `G, S0 = S`
/// - `!` becomes `!, S0 = S`
/// - `call(G)` becomes `call(G, S0, S)`
/// - `phrase(Body, ...)` keeps its arguments and gains `S0, S`
/// - `\+ G` becomes `\+ phrase(G, S0, _), S0 = S`
/// - a variable body becomes `phrase(Var, S0, S)`
/// - anything else is a nonterminal: `NT` becomes `NT(S0, S)`
///
/// [`parse_program`] / [`parse_clause`] expand `-->` clauses automatically;
/// the same expansion is available programmatically via [`dcg_rule`] and
/// [`Term::dcg_body`], and at runtime via the `phrase/2` and `phrase/3`
/// builtins.
///
/// ```mbt check
/// test {
///   let p = parse_program("as --> []. as --> [a], as.")
///   let l = variable("L")
///   let answers = p
///     .solve([compound("phrase", [atom("as"), l])])
///     .take(3)
///     .to_array()
///   assert_eq(answers[0].to_string(), "L = []")
///   assert_eq(answers[1].to_string(), "L = [a]")
///   assert_eq(answers[2].to_string(), "L = [a, a]")
///   // parsing a fixed sequence
///   let ok = p
///     .solve([compound("phrase", [atom("as"), list([atom("a"), atom("a")])])])
///     .to_array()
///   assert_eq(ok.length(), 1)
/// }
/// ```
pub fn dcg_rule(head : Term, body : Term) -> Clause {
  let s0 = variable("")
  let s = variable("")
  Clause(dcg_nonterminal(head, s0, s), body.dcg_body(s0, s))
}

///|
/// Expands a DCG body `self` (a grammar construct) into an ordinary goal
/// relating the two list arguments `s0` (input) and `s` (remaining output).
/// See the module docs for the translation rules.
pub fn Term::dcg_body(self : Term, s0 : Term, s : Term) -> Term {
  match self {
    Var(_) => compound("phrase", [self, s0, s])
    Atom("[]") => s0.eq(s)
    List(xs) => dcg_terminals(list_tail(xs, empty_list()), s0, s)
    Compound(".", [h, t]) => dcg_terminals(cons(h, t), s0, s)
    Compound(",", [a, b]) => {
      let s1 = variable("")
      a.dcg_body(s0, s1).and_(b.dcg_body(s1, s))
    }
    Compound(";", [a, b]) =>
      match a {
        // (If -> Then ; Else): expand the ->, keeping the soft cut.
        Compound("->", [c, t]) => {
          let s1 = variable("")
          Compound(";", [
            Compound("->", [c.dcg_body(s0, s1), t.dcg_body(s1, s)]),
            b.dcg_body(s0, s),
          ])
        }
        _ => a.dcg_body(s0, s).or(b.dcg_body(s0, s))
      }
    Compound("{}", [g]) => g.and_(s0.eq(s))
    Atom("!") => atom("!").and_(s0.eq(s))
    Compound("call", [g]) => compound("call", [g, s0, s])
    Compound("phrase", [b]) => compound("phrase", [b, s0, s])
    Compound("phrase", [b, a]) => compound("phrase", [b, a, s0, s])
    Compound("phrase", [b, a1, a2]) => compound("phrase", [b, a1, a2, s0, s])
    Compound("\\+", [g]) =>
      compound("\\+", [compound("phrase", [g, s0, variable("")])]).and_(
        s0.eq(s),
      )
    _ => dcg_nonterminal(self, s0, s)
  }
}

///|
/// A DCG nonterminal `NT` becomes the call `NT(S0, S)` (two extra
/// arguments); atoms become `name(S0, S)`.
fn dcg_nonterminal(nt : Term, s0 : Term, s : Term) -> Term {
  match nt {
    Atom(name) => compound(name, [s0, s])
    Compound(name, args) => {
      let full : Array[Term] = []
      for a in args {
        full.push(a)
      }
      full.push(s0)
      full.push(s)
      compound(name, full)
    }
    _ => nt
  }
}

///|
/// A terminal sequence relates `s0` to `s` by the unification
/// `S0 = Terminals + S` (cf. Scryer's `dcg_terminals/4`).
fn dcg_terminals(t : Term, s0 : Term, s : Term) -> Term {
  match list_parts(t) {
    Some((elems, tail)) =>
      if tail is Atom("[]") {
        s0.eq(list_tail(elems, s))
      } else {
        s0.eq(list_tail(elems, tail)).and_(tail.eq(s))
      }
    None => s0.eq(t)
  }
}

///|
/// `phrase(Body, S0)`: true iff `Body` describes the list `S0`; equivalent
/// to `phrase(Body, S0, [])`.
fn Machine::phrase2(self : Machine, b : Term, s0 : Term, mark : Int) -> Bool {
  match b.deref(self.subst) {
    Var(_) => false
    b => {
      self.push_goal(compound("phrase", [b, s0, empty_list()]), mark)
      true
    }
  }
}

///|
/// `phrase(Body, S0, S)`: true iff `Body` describes the part of `S0` that
/// remains `S`. The body is expanded against the current list arguments
/// (cf. Scryer's `phrase/3`).
fn Machine::phrase3(
  self : Machine,
  b : Term,
  s0 : Term,
  s : Term,
  mark : Int,
) -> Bool {
  match b.deref(self.subst) {
    Var(_) => false
    b => {
      self.push_goal(b.dcg_body(s0, s), mark)
      true
    }
  }
}
