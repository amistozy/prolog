///|
/// Evaluates a Prolog arithmetic expression under `subst`, returning the
/// value (an `Int` or `Float` term) or `None` when the expression is not
/// evaluable (e.g. contains an unbound variable or an unknown functor).
///
/// Supported functors: `+`, `-` (binary and unary), `*`, `/` (float
/// division, like ISO), `//` (integer division), `div` (floor division),
/// `mod` (floored remainder), `abs`.
fn eval_arith(t : Term, subst : Subst) -> Term? {
  match t.deref(subst) {
    Int(i) => Some(Int(i))
    Float(d) => Some(Float(d))
    Compound("-", [x]) =>
      match eval_arith(x, subst) {
        Some(Int(i)) => Some(Int(-i))
        Some(Float(d)) => Some(Float(-d))
        _ => None
      }
    Compound("abs", [x]) =>
      match eval_arith(x, subst) {
        Some(Int(i)) => Some(Int(i.abs()))
        Some(Float(d)) => Some(Float(d.abs()))
        _ => None
      }
    Compound("sqrt", [x]) =>
      match eval_arith(x, subst) {
        Some(Int(i)) => Some(Float(@math.pow(i.to_double(), 0.5)))
        Some(Float(d)) => Some(Float(@math.pow(d, 0.5)))
        _ => None
      }
    Compound(op, [x, y]) =>
      match (eval_arith(x, subst), eval_arith(y, subst)) {
        (Some(Int(a)), Some(Int(b))) => int_op(op, a, b)
        (Some(Float(a)), Some(Float(b))) => float_op(op, a, b)
        (Some(Int(a)), Some(Float(b))) => float_op(op, a.to_double(), b)
        (Some(Float(a)), Some(Int(b))) => float_op(op, a, b.to_double())
        _ => None
      }
    _ => None
  }
}

///|
fn int_op(op : String, a : Int, b : Int) -> Term? {
  match op {
    "+" => Some(Int(a + b))
    "-" => Some(Int(a - b))
    "*" => Some(Int(a * b))
    "/" =>
      if b == 0 {
        None
      } else {
        Some(Float(a.to_double() / b.to_double()))
      }
    "//" => if b == 0 { None } else { Some(Int(a / b)) }
    "div" => if b == 0 { None } else { Some(Int(floor_div(a, b))) }
    "mod" => if b == 0 { None } else { Some(Int(a - b * floor_div(a, b))) }
    "max" => Some(Int(if a > b { a } else { b }))
    "min" => Some(Int(if a < b { a } else { b }))
    "^" =>
      if b >= 0 {
        Some(Int(int_pow(a, b)))
      } else {
        Some(Float(@math.pow(a.to_double(), b.to_double())))
      }
    _ => None
  }
}

///|
fn int_pow(a : Int, b : Int) -> Int {
  let mut acc = 1
  for _ in 0..<b {
    acc = acc * a
  }
  acc
}

///|
fn float_op(op : String, a : Double, b : Double) -> Term? {
  match op {
    "+" => Some(Float(a + b))
    "-" => Some(Float(a - b))
    "*" => Some(Float(a * b))
    "/" => if b == 0.0 { None } else { Some(Float(a / b)) }
    "max" => Some(Float(if a > b { a } else { b }))
    "min" => Some(Float(if a < b { a } else { b }))
    "^" => Some(Float(@math.pow(a, b)))
    _ => None
  }
}

///|
/// Floor division: `floor_div(7, 2) = 3`, `floor_div(-7, 2) = -4`.
fn floor_div(a : Int, b : Int) -> Int {
  let q = a / b
  let r = a % b
  if r != 0 && (r < 0) != (b < 0) {
    q - 1
  } else {
    q
  }
}

///|
/// Compares two arithmetic expressions under `subst`.
fn eval_compare(op : String, a : Term, b : Term, subst : Subst) -> Bool? {
  match (eval_arith(a, subst), eval_arith(b, subst)) {
    (Some(Int(x)), Some(Int(y))) => Some(cmp_int(op, x, y))
    (Some(Float(x)), Some(Float(y))) => Some(cmp_double(op, x, y))
    (Some(Int(x)), Some(Float(y))) => Some(cmp_double(op, x.to_double(), y))
    (Some(Float(x)), Some(Int(y))) => Some(cmp_double(op, x, y.to_double()))
    _ => None
  }
}

///|
fn cmp_int(op : String, x : Int, y : Int) -> Bool {
  match op {
    "<" => x < y
    ">" => x > y
    "=<" | "<=" => x <= y
    ">=" => x >= y
    "=:=" => x == y
    "=\\=" => x != y
    _ => false
  }
}

///|
fn cmp_double(op : String, x : Double, y : Double) -> Bool {
  match op {
    "<" => x < y
    ">" => x > y
    "=<" | "<=" => x <= y
    ">=" => x >= y
    "=:=" => x == y
    "=\\=" => x != y
    _ => false
  }
}

///|
/// `==/2`-style identity on dereferenced terms: two unbound variables are
/// identical iff they share the same id.
fn identical_terms(deref_a : Term, deref_b : Term) -> Bool {
  match (deref_a, deref_b) {
    (Var(x), Var(y)) => x.id == y.id
    _ => deref_a == deref_b
  }
}

///|
/// Type tests: `var`, `nonvar`, `atom`, `integer`, `float`, `number`,
/// `atomic`, `string`, `compound`, `list`.
fn type_test(name : String, g : Term, subst : Subst) -> Bool {
  let t = g.deref(subst)
  match name {
    "var" => t is Var(_)
    "nonvar" => !(t is Var(_))
    "atom" => t is Atom(_)
    "integer" => t is Int(_)
    "float" => t is Float(_)
    "number" => t is Int(_) || t is Float(_)
    "atomic" => t is Atom(_) || t is Int(_) || t is Float(_) || t is Str(_)
    "string" => t is Str(_)
    "compound" => t is Compound(_, _) || t is List(_)
    "list" => list_parts(t) is Some(_)
    _ => false
  }
}

///|
/// Executes a builtin predicate. Returns `Some(result)` when `(name, arity)`
/// is a builtin, `None` when it should fall through to user clauses.
fn Machine::run_builtin(
  self : Machine,
  name : String,
  args : Array[Term],
  mark : Int,
) -> Bool? {
  match (name, args.length()) {
    ("=", 2) => Some(self.unify_goal(args[0], args[1]))
    ("\\=", 2) => Some(args[0].unify(args[1], self.subst) is None)
    ("dif", 2) => Some(self.dif_(args[0], args[1]))
    ("==", 2) =>
      Some(
        identical_terms(args[0].deref(self.subst), args[1].deref(self.subst)),
      )
    ("\\==", 2) =>
      Some(
        !identical_terms(args[0].deref(self.subst), args[1].deref(self.subst)),
      )
    ("is", 2) =>
      match eval_arith(args[1], self.subst) {
        Some(v) => Some(self.unify_goal(args[0], v))
        None => Some(false)
      }
    ("<", 2)
    | (">", 2)
    | ("=<", 2)
    | ("<=", 2)
    | (">=", 2)
    | ("=:=", 2)
    | ("=\\=", 2) =>
      match eval_compare(name, args[0], args[1], self.subst) {
        Some(b) => Some(b)
        None => Some(false)
      }
    ("not", 1) => Some(self.not_(args[0]))
    ("call", 1) => {
      self.push_goal(args[0], mark)
      Some(true)
    }
    ("call", 2)
    | ("call", 3)
    | ("call", 4)
    | ("call", 5)
    | ("call", 6)
    | ("call", 7)
    | ("call", 8) => Some(self.call_n_(args, mark))
    ("ignore", 1) => {
      // ignore(G): call G, succeed whether or not G has a solution.
      self.push_goal(
        Compound(";", [Compound("->", [args[0], atom("true")]), atom("true")]),
        mark,
      )
      Some(true)
    }
    ("copy_term", 2) =>
      Some(self.unify_goal(args[1], fresh_vars(args[0].resolve(self.subst))))
    ("term_variables", 2) => {
      let resolved = args[0].resolve(self.subst)
      let seen : Map[Int, Unit] = Map([])
      let vs : Array[VarRef] = []
      collect_vars_into(resolved, seen, vs)
      Some(self.unify_goal(args[1], list(vs.map(v => Var(v)))))
    }
    ("phrase", 2) => Some(self.phrase2_(args[0], args[1], mark))
    ("phrase", 3) => Some(self.phrase3_(args[0], args[1], args[2], mark))
    ("atom_codes", 2) => Some(self.atom_codes_(args[0], args[1]))
    ("atom_chars", 2) => Some(self.atom_chars_(args[0], args[1]))
    ("number_codes", 2) => Some(self.number_chars_(args[0], args[1], true))
    ("number_chars", 2) => Some(self.number_chars_(args[0], args[1], false))
    ("char_code", 2) => Some(self.char_code_(args[0], args[1]))
    ("atom_number", 2) => Some(self.atom_number_(args[0], args[1]))
    ("sub_atom", 5) => Some(self.sub_atom_(args, mark))
    ("bagof", 3) => Some(self.bagof_(args[0], args[1], args[2], false, mark))
    ("setof", 3) => Some(self.bagof_(args[0], args[1], args[2], true, mark))
    ("write", 1) => {
      println(args[0].resolve(self.subst))
      Some(true)
    }
    ("writeln", 1) => {
      println(args[0].resolve(self.subst))
      Some(true)
    }
    ("var", 1)
    | ("nonvar", 1)
    | ("atom", 1)
    | ("integer", 1)
    | ("float", 1)
    | ("number", 1)
    | ("atomic", 1)
    | ("string", 1)
    | ("compound", 1)
    | ("list", 1) => Some(type_test(name, args[0], self.subst))
    ("\\+", 1) => Some(self.not_(args[0]))
    ("once", 1) => {
      let m = self.choices.length()
      self.push_goal(atom("!"), m)
      self.push_goal(args[0], m)
      Some(true)
    }
    ("repeat", 0) => {
      self.push_choice(Goal(goal=atom("repeat"), mark~))
      Some(true)
    }
    ("findall", 3) => Some(self.findall_(args[0], args[1], args[2]))
    ("forall", 2) => Some(self.not_(args[0].and_(args[1].not_())))
    ("functor", 3) => Some(self.functor_(args[0], args[1], args[2]))
    ("arg", 3) => Some(self.arg_(args[0], args[1], args[2]))
    ("=..", 2) => Some(self.univ_(args[0], args[1]))
    ("ground", 1) => Some(is_ground(args[0].resolve(self.subst)))
    ("compare", 3) => {
      let c = args[1]
        .resolve(self.subst)
        .compare_terms(args[2].resolve(self.subst))
      let ord = if c < 0 { "<" } else if c > 0 { ">" } else { "=" }
      Some(self.unify_goal(args[0], atom(ord)))
    }
    ("sort", 2) | ("msort", 2) => Some(self.sort_(name, args[0], args[1]))
    ("@<", 2) | ("@>", 2) | ("@=<", 2) | ("@>=", 2) => {
      let c = args[0]
        .resolve(self.subst)
        .compare_terms(args[1].resolve(self.subst))
      Some(
        match name {
          "@<" => c < 0
          "@>" => c > 0
          "@=<" => c <= 0
          _ => c >= 0
        },
      )
    }
    ("atom_length", 2) =>
      match args[0].deref(self.subst) {
        Atom(s) => Some(self.unify_goal(args[1], int(s.length())))
        Str(s) => Some(self.unify_goal(args[1], int(s.length())))
        _ => Some(false)
      }
    ("atom_concat", 3) =>
      Some(self.atom_concat_(args[0], args[1], args[2], mark))
    _ => None
  }
}

///|
/// Unifies two terms under the machine's substitution, updating it on
/// success. Fails (and leaves the substitution for backtracking to undo)
/// when the binding violates an active `dif/2` constraint.
fn Machine::unify_goal(self : Machine, a : Term, b : Term) -> Bool {
  match a.unify(b, self.subst) {
    Some(s) => self.commit(s)
    None => false
  }
}
