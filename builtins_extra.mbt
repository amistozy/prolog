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
fn Machine::findall_(
  self : Machine,
  template : Term,
  goal : Term,
  result : Term,
) -> Bool {
  let saved_stack = self.stack
  let saved_subst = self.subst
  let cb = self.choices.length()
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
fn Machine::functor_(self : Machine, t : Term, f : Term, n : Term) -> Bool {
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
        Some(s3) => {
          self.subst = s3
          true
        }
      }
  }
}

///|
/// `arg(N, T, A)`: the N-th argument (1-based) of a compound term or list.
fn Machine::arg_(self : Machine, i : Term, t : Term, a : Term) -> Bool {
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
fn Machine::univ_(self : Machine, t : Term, l : Term) -> Bool {
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
/// `sort` also removes duplicates.
fn Machine::sort_(self : Machine, name : String, l : Term, s : Term) -> Bool {
  match list_parts(l.deref(self.subst)) {
    Some((elems, tail)) if tail is Atom("[]") => {
      let resolved = elems.map(x => x.resolve(self.subst))
      resolved.sort_by(Term::compare_terms)
      let dedup = if name == "sort" {
        let out : Array[Term] = []
        for x in resolved {
          if out.length() == 0 || out[out.length() - 1].compare_terms(x) != 0 {
            out.push(x)
          }
        }
        out
      } else {
        resolved
      }
      self.unify_goal(s, list(dedup))
    }
    _ => false
  }
}

///|
/// `atom_concat(A, B, C)`: concatenates two atoms; when only `C` is ground,
/// enumerates all splits via choice points.
fn Machine::atom_concat_(
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
        self.choices.push({
          goals: self.stack,
          subst: self.subst,
          alt: Goal(goal=a.eq(atom(prefix)).and_(b.eq(atom(suffix))), mark~),
        })
      }
      self.unify_goal(a, atom("")) && self.unify_goal(b, atom(z))
    }
    _ => false
  }
}
