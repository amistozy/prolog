///|
/// Meta and term-manipulation builtins: `findall/3`, `functor/3`, `arg/3`,
/// `=../2`, `ground/1`, `sort/2`, `msort/2`, `atom_concat/3`.
///
/// The implementations run on the engine directly (like Scryer's builtins
/// are compiled into the machine).

///|
/// `findall(T, G, L)`: collects one fresh-variable-copied instance of `T`
/// for every solution of `G`, in order. Like `not/1`, the sub-search runs
/// with barriers so it cannot disturb the outer search.
fn Machine::findall(
  self : Machine,
  template : Term,
  goal : Term,
  result : Term,
) -> Bool {
  let saved_stack = self.stack
  let saved_subst = self.subst
  let cb = self.choices.length()
  let db = self.diffs.length()
  let results : Array[Term] = []
  self.push_goal(goal, cb)
  for ;; {
    match self.step(saved_stack, cb) {
      Some(s) => {
        let t = template.resolve(s)
        results.push(fresh_vars(t))
      }
      None => break
    }
  }
  self.stack = saved_stack
  self.subst = saved_subst
  self.choices.truncate(cb)
  self.diffs.truncate(db)
  self.resumed = false
  self.unify_goal(result, list(results))
}

///|
/// Renames every variable of `t` to a fresh id (used by `findall/3` to make
/// solutions independent of the query's variables).
fn fresh_vars(t : Term) -> Term {
  let ids = collect_var_ids(t, Map([]))
  let map : Map[Int, Int] = Map([])
  for id, _ in ids {
    map[id] = fresh_id()
  }
  rename_vars(t, map)
}

///|
/// `functor(T, F, N)`: the name/arity of a ground term, or builds a term
/// from a name and arity when `T` is a variable.
fn Machine::functor(self : Machine, t : Term, f : Term, n : Term) -> Bool {
  match t.deref(self.subst) {
    Atom(name) => self.unify_both(f, atom(name), n, int(0))
    Int(i) => self.unify_both(f, Int(i), n, int(0))
    Float(d) => self.unify_both(f, Float(d), n, int(0))
    Str(s) => self.unify_both(f, str(s), n, int(0))
    List(_) => self.unify_both(f, atom("."), n, int(2))
    Compound(name, args) =>
      self.unify_both(f, atom(name), n, int(args.length()))
    Var(_) => {
      let f = f.deref(self.subst)
      let n = n.deref(self.subst)
      match (f, n) {
        (Atom(name), Int(0)) => self.unify_goal(t, atom(name))
        (Int(i), Int(0)) => self.unify_goal(t, Int(i))
        (Float(d), Int(0)) => self.unify_goal(t, Float(d))
        (Atom(name), Int(arity)) if arity > 0 => {
          let args : Array[Term] = []
          for _ in 0..<arity {
            args.push(variable("_"))
          }
          self.unify_goal(t, Compound(name, args))
        }
        _ => false
      }
    }
  }
}

///|
/// Unifies `a` with `va` and `b` with `vb` atomically (either both succeed
/// or the substitution is left untouched).
fn Machine::unify_both(
  self : Machine,
  a : Term,
  va : Term,
  b : Term,
  vb : Term,
) -> Bool {
  match a.unify(va, self.subst) {
    None => false
    Some(s2) =>
      match b.unify(vb, s2) {
        None => false
        Some(s3) => self.commit(s3)
      }
  }
}

///|
/// `arg(N, T, A)`: the N-th argument (1-based) of a compound term or list.
fn Machine::arg(self : Machine, i : Term, t : Term, a : Term) -> Bool {
  match (i.deref(self.subst), t.deref(self.subst)) {
    (Int(k), Compound(_, args)) if k >= 1 && k <= args.length() =>
      self.unify_goal(a, args[k - 1])
    (Int(k), List(xs)) if k >= 1 && k <= xs.length() =>
      self.unify_goal(a, xs[k - 1])
    _ => false
  }
}

///|
/// `T =.. L`: converts between a term and its functor-and-arguments list.
fn Machine::univ(self : Machine, t : Term, l : Term) -> Bool {
  match t.deref(self.subst) {
    Atom(name) => self.unify_goal(l, list([atom(name)]))
    Int(i) => self.unify_goal(l, list([Int(i)]))
    Float(d) => self.unify_goal(l, list([Float(d)]))
    Str(s) => self.unify_goal(l, list([str(s)]))
    List(xs) => {
      // [a, b] =.. ['.', a, [b]]
      let rest : Array[Term] = []
      for i in 1..<xs.length() {
        rest.push(xs[i])
      }
      self.unify_goal(
        l,
        list([atom("."), xs[0], list_tail(rest, empty_list())]),
      )
    }
    Compound(name, args) => {
      let full : Array[Term] = [atom(name)]
      for a in args {
        full.push(a)
      }
      self.unify_goal(l, list(full))
    }
    Var(_) =>
      match list_parts(l.deref(self.subst)) {
        Some((elems, tail)) if tail is Atom("[]") && elems.length() > 0 =>
          match elems[0] {
            Atom(name) => {
              let args : Array[Term] = []
              for i in 1..<elems.length() {
                args.push(elems[i])
              }
              self.unify_goal(t, Compound(name, args))
            }
            Int(i) if elems.length() == 1 => self.unify_goal(t, Int(i))
            Float(d) if elems.length() == 1 => self.unify_goal(t, Float(d))
            _ => false
          }
        _ => false
      }
  }
}

///|
/// Is `t` free of unbound variables?
fn is_ground(t : Term) -> Bool {
  match t {
    Var(_) => false
    List(xs) => xs.all(is_ground)
    Compound(_, args) => args.all(is_ground)
    _ => true
  }
}

///|
/// `sort(L, S)` / `msort(L, S)`: sort a proper list in standard order;
/// `sort` also removes duplicates (all duplicates are consecutive after
/// sorting, so `dedup` is exactly right).
fn Machine::sort(self : Machine, name : String, l : Term, s : Term) -> Bool {
  match list_parts(l.deref(self.subst)) {
    Some((elems, tail)) if tail is Atom("[]") => {
      let resolved = elems.map(x => x.resolve(self.subst))
      resolved.sort_by(Term::compare_terms)
      if name == "sort" {
        resolved.dedup()
      }
      self.unify_goal(s, list(resolved))
    }
    _ => false
  }
}

///|
/// `atom_concat(A, B, C)`: concatenates two atoms; when only `C` is ground,
/// enumerates all splits via choice points.
fn Machine::atom_concat(
  self : Machine,
  a : Term,
  b : Term,
  c : Term,
  mark : Int,
) -> Bool {
  match (a.deref(self.subst), b.deref(self.subst), c.deref(self.subst)) {
    (Atom(x), Atom(y), _) => self.unify_goal(c, atom(x + y))
    (_, _, Atom(z)) => {
      let n = z.length()
      // Push choice points for splits 1..n (popped in order 1, 2, ...), then
      // try the empty-prefix split directly.
      for i = n; i >= 1; i = i - 1 {
        let prefix = z[0:i].to_owned()
        let suffix = z[i:].to_owned()
        self.push_choice(
          Goal(goal=a.eq(atom(prefix)) & b.eq(atom(suffix)), mark~),
        )
      }
      self.unify_goal(a, atom("")) && self.unify_goal(b, atom(z))
    }
    _ => false
  }
}

///|
/// `call(G, A1, ..., An)`: appends the extra arguments to `G` and calls it.
fn Machine::call_n(self : Machine, args : Array[Term], mark : Int) -> Bool {
  let g = args[0].deref(self.subst)
  match g {
    Var(_) => false
    Atom(name) => {
      let full : Array[Term] = []
      for i in 1..<args.length() {
        full.push(args[i])
      }
      self.push_goal(compound(name, full), mark)
      true
    }
    Compound(name, gargs) => {
      let full : Array[Term] = []
      for a in gargs {
        full.push(a)
      }
      for i in 1..<args.length() {
        full.push(args[i])
      }
      self.push_goal(compound(name, full), mark)
      true
    }
    _ => false
  }
}

///|
/// Writes one character code (a UTF-16 code unit) into `sb`; `false` for
/// codes that are not valid single units (surrogates).
fn try_write_code(sb : StringBuilder, k : Int) -> Bool {
  if k < 0 || k > 0xFFFF {
    return false
  }
  match k.to_uint16().to_char() {
    Some(c) => {
      sb.write_char(c)
      true
    }
    None => false
  }
}

///|
/// `atom_codes(A, Cs)`: relates an atom to its list of character codes
/// (both directions, cf. Scryer's `builtins.pl`).
fn Machine::atom_codes(self : Machine, a : Term, cs : Term) -> Bool {
  match a.deref(self.subst) {
    Atom(s) => {
      let codes : Array[Term] = []
      for i in 0..<s.length() {
        codes.push(int(s[i].to_int()))
      }
      self.unify_goal(cs, list(codes))
    }
    Var(_) =>
      match list_parts(cs.deref(self.subst)) {
        Some((elems, tail)) if tail is Atom("[]") => {
          let sb = StringBuilder()
          for e in elems {
            match e.deref(self.subst) {
              Int(k) => if !try_write_code(sb, k) { return false }
              _ => return false
            }
          }
          self.unify_goal(a, atom(sb.to_string()))
        }
        _ => false
      }
    _ => false
  }
}

///|
/// `atom_chars(A, Cs)`: relates an atom to its list of single-character
/// atoms (both directions).
fn Machine::atom_chars(self : Machine, a : Term, cs : Term) -> Bool {
  match a.deref(self.subst) {
    Atom(s) => {
      let chars : Array[Term] = []
      for i in 0..<s.length() {
        match s[i].to_char() {
          Some(c) => chars.push(atom(c.to_string()))
          None => return false
        }
      }
      self.unify_goal(cs, list(chars))
    }
    Var(_) =>
      match list_parts(cs.deref(self.subst)) {
        Some((elems, tail)) if tail is Atom("[]") => {
          let sb = StringBuilder()
          for e in elems {
            match e.deref(self.subst) {
              Atom(s) if s.length() == 1 =>
                match s[0].to_char() {
                  Some(c) => sb.write_char(c)
                  None => return false
                }
              _ => return false
            }
          }
          self.unify_goal(a, atom(sb.to_string()))
        }
        _ => false
      }
    _ => false
  }
}

///|
/// Builds a list of codes or single-character atoms from a string.
fn text_to_list(s : String, codes : Bool) -> Term {
  let elems : Array[Term] = []
  for i in 0..<s.length() {
    let u = s[i]
    if codes {
      elems.push(int(u.to_int()))
    } else {
      let sb = StringBuilder()
      sb.write_char(u.to_char().unwrap_or('?'))
      elems.push(atom(sb.to_string()))
    }
  }
  list(elems)
}

///|
/// Reconstructs the string of a ground codes/chars list, or `None` when an
/// element is not a code / single-character atom.
fn list_to_text(elems : Array[Term], subst : Subst, codes : Bool) -> String? {
  let sb = StringBuilder()
  for e in elems {
    match e.deref(subst) {
      Int(k) if codes => if !try_write_code(sb, k) { return None }
      Atom(s) if !codes && s.length() == 1 =>
        match s[0].to_char() {
          Some(c) => sb.write_char(c)
          None => return None
        }
      _ => return None
    }
  }
  Some(sb.to_string())
}

///|
/// Parses an integer or float literal, or `None` when `s` is not a number.
fn parse_number_text(s : String) -> Term? {
  match try_parse_int(s) {
    Some(v) => Some(Int(v))
    None =>
      match try_parse_double(s) {
        Some(v) => Some(Float(v))
        None => None
      }
  }
}

///|
fn try_parse_int(s : String) -> Int? {
  Some(@string.parse_int(s)) catch {
    _ => None
  }
}

///|
fn try_parse_double(s : String) -> Double? {
  Some(@string.parse_double(s)) catch {
    _ => None
  }
}

///|
/// `number_codes(N, Cs)` / `number_chars(N, Cs)`: relates a number to its
/// textual representation as codes or chars (both directions).
fn Machine::number_chars(
  self : Machine,
  n : Term,
  cs : Term,
  codes : Bool,
) -> Bool {
  match n.deref(self.subst) {
    Int(i) => self.unify_goal(cs, text_to_list(i.to_string(), codes))
    Float(d) => self.unify_goal(cs, text_to_list(d.to_string(), codes))
    Var(_) =>
      match list_parts(cs.deref(self.subst)) {
        Some((elems, tail)) if tail is Atom("[]") =>
          match list_to_text(elems, self.subst, codes) {
            None => false
            Some(s) =>
              match parse_number_text(s) {
                None => false
                Some(v) => self.unify_goal(n, v)
              }
          }
        _ => false
      }
    _ => false
  }
}

///|
/// `char_code(C, K)`: relates a single-character atom to its code (a UTF-16
/// code unit).
fn Machine::char_code(self : Machine, c : Term, k : Term) -> Bool {
  match c.deref(self.subst) {
    Atom(s) if s.length() == 1 => self.unify_goal(k, int(s[0].to_int()))
    Var(_) =>
      match k.deref(self.subst) {
        Int(code) =>
          if code >= 0 && code <= 0xFFFF {
            match code.to_uint16().to_char() {
              Some(ch) => self.unify_goal(c, atom(ch.to_string()))
              None => false
            }
          } else {
            false
          }
        _ => false
      }
    _ => false
  }
}

///|
/// `atom_number(A, N)`: relates an atom to the number it spells (both
/// directions).
fn Machine::atom_number(self : Machine, a : Term, n : Term) -> Bool {
  match a.deref(self.subst) {
    Atom(s) =>
      match parse_number_text(s) {
        Some(v) => self.unify_goal(n, v)
        None => false
      }
    Var(_) =>
      match n.deref(self.subst) {
        Int(i) => self.unify_goal(a, atom(i.to_string()))
        Float(d) => self.unify_goal(a, atom(d.to_string()))
        _ => false
      }
    _ => false
  }
}

///|
/// `sub_atom(A, B, L, Af, S)`: relates an atom to a sub-atom starting at
/// position `B` with length `L`, leaving `Af` characters after it. When `A`
/// is ground, enumerates all matching splits (cf. Scryer's `builtins.pl`).
fn Machine::sub_atom(self : Machine, args : Array[Term], mark : Int) -> Bool {
  match args[0].deref(self.subst) {
    Atom(s) => {
      let n = s.length()
      // Ground positions prune the enumeration.
      let b0 : Int? = match args[1].deref(self.subst) {
        Int(k) if k >= 0 => Some(k)
        Int(_) => return false
        _ => None
      }
      let l0 : Int? = match args[2].deref(self.subst) {
        Int(k) if k >= 0 => Some(k)
        Int(_) => return false
        _ => None
      }
      let af0 : Int? = match args[3].deref(self.subst) {
        Int(k) if k >= 0 => Some(k)
        Int(_) => return false
        _ => None
      }
      let splits : Array[(Int, Int)] = []
      for b in 0..<=n {
        for l in 0..<=(n - b) {
          let af = n - b - l
          let ok = (b0 is None || b0.unwrap() == b) &&
            (l0 is None || l0.unwrap() == l) &&
            (af0 is None || af0.unwrap() == af)
          if ok {
            splits.push((b, l))
          }
        }
      }
      if splits.length() == 0 {
        return false
      }
      for i = splits.length() - 1; i >= 1; i = i - 1 {
        let (b, l) = splits[i]
        let af = n - b - l
        self.push_choice(
          Goal(
            goal=args[1].eq(int(b)) &
              args[2].eq(int(l)) &
              args[3].eq(int(af)) &
              args[4].eq(atom(s[b:b + l].to_owned())),
            mark~,
          ),
        )
      }
      let (b, l) = splits[0]
      let af = n - b - l
      self.unify_goal(args[1], int(b)) &&
      self.unify_goal(args[2], int(l)) &&
      self.unify_goal(args[3], int(af)) &&
      self.unify_goal(args[4], atom(s[b:b + l].to_owned()))
    }
    _ => false
  }
}

///|
/// `bagof(T, G, S)` / `setof(T, G, S)`: collects the solutions of `G` into
/// lists grouped by the values of `G`'s free variables that do not occur in
/// `T` (the witnesses), like Scryer's `builtins.pl`. `Var ^ G` marks
/// existential variables, which do not group solutions. `bagof` fails when
/// `G` has no solutions; `setof` also sorts each group and removes
/// duplicates (in standard order).
///
/// Groups are produced in order of first appearance of the witness values
/// (Scryer orders them by the standard term order instead); witnesses that
/// remain unbound all fall into one group.
fn Machine::bagof(
  self : Machine,
  template : Term,
  goal : Term,
  result : Term,
  set : Bool,
  mark : Int,
) -> Bool {
  // strip leading existentials: X1 ^ X2 ^ ... ^ G
  let mut g = goal.deref(self.subst)
  let ex : Map[Int, Unit] = Map([])
  for ;; {
    match g {
      Compound("^", [x, rest]) => {
        let _ = collect_var_ids(x, ex)
        g = rest
      }
      _ => break
    }
  }
  // witnesses: variables of g, excluding template and existential variables
  let excl : Map[Int, Unit] = Map([])
  let _ = collect_var_ids(template, excl)
  for id, _ in ex {
    excl[id] = ()
  }
  let wvars : Array[VarRef] = []
  {
    let seen : Map[Int, Unit] = Map([])
    collect_witnesses(g, excl, seen, wvars)
  }
  // collect (witness tuple, template copy) per solution
  let saved_stack = self.stack
  let saved_subst = self.subst
  let cb = self.choices.length()
  let db = self.diffs.length()
  let pairs : Array[(Term, Term)] = []
  self.push_goal(g, cb)
  for ;; {
    match self.step(saved_stack, cb) {
      Some(s) => {
        let w : Array[Term] = []
        for v in wvars {
          w.push(Var(v).resolve(s))
        }
        pairs.push((fresh_vars(list(w)), fresh_vars(template.resolve(s))))
      }
      None => break
    }
  }
  self.stack = saved_stack
  self.subst = saved_subst
  self.choices.truncate(cb)
  self.diffs.truncate(db)
  self.resumed = false
  if pairs.length() == 0 {
    return false
  }
  // group by variant equality of the witness tuple, in order of first
  // appearance
  let groups : Array[(Term, Array[Term])] = []
  for p in pairs {
    let (w, t) = p
    let mut found = -1
    for i in 0..<groups.length() {
      if variant_eq(groups[i].0, w) {
        found = i
        break
      }
    }
    if found >= 0 {
      groups[found].1.push(t)
    } else {
      groups.push((w, [t]))
    }
  }
  if set {
    for i in 0..<groups.length() {
      let elems = groups[i].1
      elems.sort_by(Term::compare_terms)
      elems.dedup()
    }
  }
  for i = groups.length() - 1; i >= 1; i = i - 1 {
    self.push_choice(Goal(goal=result.eq(list(groups[i].1)), mark~))
  }
  self.unify_goal(result, list(groups[0].1))
}

///|
/// Collects the variables of `t` that are not excluded, in order of first
/// appearance.
fn collect_witnesses(
  t : Term,
  excl : Map[Int, Unit],
  seen : Map[Int, Unit],
  out : Array[VarRef],
) -> Unit {
  match t {
    Var(v) =>
      if !excl.contains(v.id) && !seen.contains(v.id) {
        seen[v.id] = ()
        out.push(v)
      }
    List(xs) =>
      for x in xs {
        collect_witnesses(x, excl, seen, out)
      }
    Compound(_, args) =>
      for x in args {
        collect_witnesses(x, excl, seen, out)
      }
    _ => ()
  }
}

///|
/// Variant equality: structural equality where any two unbound variables
/// are considered equal (used to group `bagof`/`setof` solutions by
/// witness values).
fn variant_eq(a : Term, b : Term) -> Bool {
  match (a, b) {
    (Var(_), Var(_)) => true
    (Int(x), Int(y)) => x == y
    (Float(x), Float(y)) => x == y
    (Atom(x), Atom(y)) => x == y
    (Str(x), Str(y)) => x == y
    (List(xs), List(ys)) => variant_eq_list(xs, ys)
    (Compound(f1, a1), Compound(f2, a2)) => f1 == f2 && variant_eq_list(a1, a2)
    _ => false
  }
}

///|
fn variant_eq_list(a : Array[Term], b : Array[Term]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  a
  .zip(b)
  .all(p => {
    let (x, y) = p
    variant_eq(x, y)
  })
}
