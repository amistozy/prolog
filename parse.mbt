///|
/// A parser for a practical subset of Prolog syntax: terms, clauses and
/// whole programs (see `reference/scryer-prolog/src/parser` for the full
/// Scryer parser; this one covers the common cases with ISO operator
/// precedences).
///
/// Supported syntax:
///
/// - variables: `X`, `_Foo`, `_` (each `_` is a fresh anonymous variable)
/// - atoms: `foo`, quoted `'foo bar'`, `!`
/// - numbers: `42`, `-3`, `1.5`, `1.5e-2` (a leading `-` builds `-(N)`)
/// - strings: `"hello"` (with `\"`, `\\`, `\n`, `\t` escapes)
/// - lists: `[]`, `[a, b]`, `[a, b | T]`
/// - compound terms and operators: `f(a, b)`, `a + b * c`,
///   `(a, b) ; c`, `X is 2 * 3`, `X =.. [f, a]`
/// - clauses: `head :- body.` / `fact.` — with `%` and `/* */` comments
///
/// ```mbt check
/// test {
///   inspect(parse_term("parent(john, X)").to_string(), content="parent(john, X)")
///   inspect(parse_term("1 + 2 * 3").to_string(), content="(1 + (2 * 3))")
///   inspect(parse_term("[a, b | T]").to_string(), content="[a, b | T]")
///   inspect(parse_term("(a, b) ; c").to_string(), content="(a, b; c)")
/// }
/// ```
pub fn parse_term(text : String) -> Term raise ParseError {
  let p = Parser::new(tokenize(text))
  let t = parse_expr(p, 1200)
  expect_eof(p)
  t
}

///|
/// Parses one clause: `head :- body.` or a bare fact `head.` (the trailing
/// period is optional).
///
/// ```mbt check
/// test {
///   let c = parse_clause("ancestor(X, Y) :- parent(X, Y).")
///   inspect(c.head.to_string(), content="ancestor(X, Y)")
///   inspect(c.body.to_string(), content="parent(X, Y)")
///   inspect(parse_clause("likes(john, mary).").body.to_string(), content="true")
/// }
/// ```
pub fn parse_clause(text : String) -> Clause raise ParseError {
  let p = Parser::new(tokenize(text))
  let t = parse_expr(p, 1200)
  match p.peek() {
    TkPeriod => p.advance()
    _ => ()
  }
  expect_eof(p)
  match t {
    Compound(":-", [head, body]) => rule(head, body)
    _ => fact(t)
  }
}

///|
/// Parses a whole program (a sequence of clauses separated by `.`), e.g.
///
/// ```mbt check
/// test {
///   let p = parse_program(
///     "parent(john, mary). parent(john, jane).\n% ancestor rule\nancestor(X, Y) :- parent(X, Y).",
///   )
///   let x = variable("X")
///   let answers = p.solve([compound("parent", [x, variable("_")])]).to_array()
///   assert_eq(answers.length(), 2)
/// }
/// ```
pub fn parse_program(text : String) -> Program raise ParseError {
  let p = Parser::new(tokenize(text))
  let clauses : Array[Clause] = []
  for ;; {
    // skip stray periods
    while p.peek() is TkPeriod {
      p.advance()
    }
    if p.peek() is TkEof {
      break
    }
    // Each clause has its own variable scope.
    p.vars = Map([])
    let t = parse_expr(p, 1200)
    match p.peek() {
      TkPeriod => p.advance()
      _ => ()
    }
    match t {
      Compound(":-", [head, body]) => clauses.push(rule(head, body))
      _ => clauses.push(fact(t))
    }
  }
  try! program(clauses)
}

///|
/// Errors produced by the parser.
pub(all) suberror ParseError {
  UnexpectedChar(pos~ : Int, ch~ : Char)
  UnexpectedEof(pos~ : Int)
  UnclosedString(pos~ : Int)
} derive(Debug)

///|
struct TokItem {
  tok : Tok
  pos : Int
} derive(Debug)

///|
enum Tok {
  TkVar(String)
  TkAtom(String)
  TkInt(Int)
  TkFloat(Double)
  TkStr(String)
  TkSym(String)
  TkLParen
  TkRParen
  TkLBracket
  TkRBracket
  TkPipe
  TkPeriod
  TkEof
} derive(Debug)

///|
struct Parser {
  toks : Array[TokItem]
  mut pos : Int
  /// Named variables of the term/clause being parsed: the same name must
  /// denote the same logic variable (like in Prolog source text).
  mut vars : Map[String, Term]
} derive(Debug)

///|
fn Parser::new(toks : Array[TokItem]) -> Parser {
  { toks, pos: 0, vars: Map([]) }
}

///|
fn Parser::peek(self : Parser) -> Tok {
  if self.pos < self.toks.length() {
    self.toks[self.pos].tok
  } else {
    TkEof
  }
}

///|
fn Parser::advance(self : Parser) -> Unit {
  self.pos = self.pos + 1
}

///|
fn is_digit(c : UInt16) -> Bool {
  c >= '0' && c <= '9'
}

///|
fn is_letter(c : UInt16) -> Bool {
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
}

///|
fn is_alnum(c : UInt16) -> Bool {
  is_digit(c) || is_letter(c)
}

///|
fn is_symbol_char(c : UInt16) -> Bool {
  match c {
    '+'
    | '-'
    | '*'
    | '/'
    | '\\'
    | '='
    | '<'
    | '>'
    | '@'
    | '#'
    | '$'
    | '&'
    | '^'
    | '~'
    | ':'
    | ';'
    | ','
    | '!'
    | '.' => true
    _ => false
  }
}

///|
/// Appends a UTF-16 code unit as a char (surrogates are decoded by
/// `UInt16::to_char`).
fn sb_write_unit(sb : StringBuilder, u : UInt16) -> Unit {
  match u.to_char() {
    Some(c) => sb.write_char(c)
    None => ()
  }
}

///|
/// Tokenizes Prolog source text.
fn tokenize(text : String) -> Array[TokItem] raise ParseError {
  let toks : Array[TokItem] = []
  let n = text.length()
  let mut i = 0
  while i < n {
    let c = text[i]
    // whitespace
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
      i = i + 1
      continue
    }
    // line comment
    if c == '%' {
      while i < n && text[i] != '\n' {
        i = i + 1
      }
      continue
    }
    // block comment
    if c == '/' && i + 1 < n && text[i + 1] == '*' {
      let mut j = i + 2
      while j + 1 < n && !(text[j] == '*' && text[j + 1] == '/') {
        j = j + 1
      }
      i = j + 2
      continue
    }
    // punctuation
    if c == '(' {
      toks.push({ tok: TkLParen, pos: i })
      i = i + 1
      continue
    }
    if c == ')' {
      toks.push({ tok: TkRParen, pos: i })
      i = i + 1
      continue
    }
    if c == '[' {
      toks.push({ tok: TkLBracket, pos: i })
      i = i + 1
      continue
    }
    if c == ']' {
      toks.push({ tok: TkRBracket, pos: i })
      i = i + 1
      continue
    }
    if c == '|' {
      toks.push({ tok: TkPipe, pos: i })
      i = i + 1
      continue
    }
    // identifiers: variables start with an uppercase letter or `_`
    if is_letter(c) || c == '_' {
      let start = i
      while i < n && (is_alnum(text[i]) || text[i] == '_') {
        i = i + 1
      }
      let name = text[start:i].to_owned()
      if (c >= 'A' && c <= 'Z') || c == '_' {
        toks.push({ tok: TkVar(name), pos: start })
      } else {
        toks.push({ tok: TkAtom(name), pos: start })
      }
      continue
    }
    // numbers
    if is_digit(c) {
      let start = i
      while i < n && is_digit(text[i]) {
        i = i + 1
      }
      if i < n && text[i] == '.' && i + 1 < n && is_digit(text[i + 1]) {
        i = i + 1
        while i < n && is_digit(text[i]) {
          i = i + 1
        }
        if i < n && (text[i] == 'e' || text[i] == 'E') {
          let j = i + 1
          let mut k = j
          if k < n && (text[k] == '+' || text[k] == '-') {
            k = k + 1
          }
          if k < n && is_digit(text[k]) {
            i = k
            while i < n && is_digit(text[i]) {
              i = i + 1
            }
          }
        }
        toks.push({
          tok: TkFloat(parse_float_text(text[start:i].to_owned())),
          pos: start,
        })
      } else {
        toks.push({
          tok: TkInt(parse_int_text(text[start:i].to_owned())),
          pos: start,
        })
      }
      continue
    }
    // strings
    if c == '"' {
      let start = i
      i = i + 1
      let sb = StringBuilder()
      let mut closed = false
      while i < n {
        let ch = text[i]
        if ch == '"' {
          i = i + 1
          closed = true
          break
        }
        if ch == '\\' && i + 1 < n {
          let e = text[i + 1]
          match e {
            'n' => sb.write_char('\n')
            't' => sb.write_char('\t')
            '\\' => sb.write_char('\\')
            '"' => sb.write_char('"')
            _ => sb_write_unit(sb, e)
          }
          i = i + 2
          continue
        }
        sb_write_unit(sb, ch)
        i = i + 1
      }
      if !closed {
        raise ParseError::UnclosedString(pos=start)
      }
      toks.push({ tok: TkStr(sb.to_string()), pos: start })
      continue
    }
    // quoted atoms: 'foo bar' ('' escapes a quote)
    if c == '\'' {
      let start = i
      i = i + 1
      let sb = StringBuilder()
      let mut closed = false
      while i < n {
        let ch = text[i]
        if ch == '\'' {
          if i + 1 < n && text[i + 1] == '\'' {
            sb.write_char('\'')
            i = i + 2
            continue
          }
          i = i + 1
          closed = true
          break
        }
        sb_write_unit(sb, ch)
        i = i + 1
      }
      if !closed {
        raise ParseError::UnclosedString(pos=start)
      }
      toks.push({ tok: TkAtom(sb.to_string()), pos: start })
      continue
    }
    // symbols (operators); a lone `.` followed by a non-symbol is a period
    if is_symbol_char(c) {
      if c == '.' && (i + 1 >= n || !is_symbol_char(text[i + 1])) {
        toks.push({ tok: TkPeriod, pos: i })
        i = i + 1
        continue
      }
      let start = i
      while i < n && is_symbol_char(text[i]) {
        i = i + 1
      }
      toks.push({ tok: TkSym(text[start:i].to_owned()), pos: start })
      continue
    }
    raise ParseError::UnexpectedChar(pos=i, ch=text.get_char(i).unwrap_or('?'))
  }
  toks.push({ tok: TkEof, pos: n })
  toks
}

///|
/// Parses `123`.
fn parse_int_text(s : String) -> Int {
  let mut v = 0
  for ch in s {
    v = v * 10 + (ch.to_int() - '0'.to_int())
  }
  v
}

///|
/// Parses `1.5` / `1.5e-2` (no sign; unary `-` builds `-(N)`).
fn parse_float_text(s : String) -> Double {
  let mut mantissa = 0.0
  let mut frac_scale = 1.0
  let mut seen_dot = false
  let mut exp = 0
  let mut exp_sign = 1
  let mut reading_exp = false
  for ch in s {
    if ch == '.' {
      seen_dot = true
    } else if ch == 'e' || ch == 'E' {
      reading_exp = true
    } else if reading_exp && ch == '-' {
      exp_sign = -1
    } else if reading_exp && ch == '+' {
      ()
    } else if reading_exp {
      exp = exp * 10 + (ch.to_int() - '0'.to_int())
    } else if seen_dot {
      frac_scale = frac_scale / 10.0
      mantissa = mantissa +
        (ch.to_int() - '0'.to_int()).to_double() * frac_scale
    } else {
      mantissa = mantissa * 10.0 + (ch.to_int() - '0'.to_int()).to_double()
    }
  }
  let mut result = mantissa
  if exp_sign < 0 {
    for _ in 0..<exp {
      result = result / 10.0
    }
  } else {
    for _ in 0..<exp {
      result = result * 10.0
    }
  }
  result
}

///|
/// Infix operator table: (precedence, associativity). ISO precedences.
fn infix_op(s : String) -> (Int, String)? {
  match s {
    ":-" => Some((1200, "xfx"))
    ";" => Some((1100, "xfy"))
    "->" => Some((1050, "xfy"))
    "," => Some((1000, "xfy"))
    "="
    | "\\="
    | "=="
    | "\\=="
    | "=:="
    | "=\\="
    | "<"
    | ">"
    | "=<"
    | ">="
    | "is"
    | "=.."
    | "@<"
    | "@>"
    | "@=<"
    | "@>=" => Some((700, "xfx"))
    "+" | "-" => Some((500, "yfx"))
    "*" | "/" | "//" | "div" | "mod" => Some((400, "yfx"))
    "^" => Some((200, "xfy"))
    _ => None
  }
}

///|
/// Prefix operator table: (precedence).
fn prefix_op(s : String) -> Int? {
  match s {
    "-" | "+" | "\\+" => Some(200)
    _ => None
  }
}

///|
/// Parses an expression, consuming infix operators with precedence at most
/// `max_prec` (precedence climbing; the right-hand side bound depends on
/// associativity: yfx -> prec - 1, xfy -> prec, xfx -> prec - 1).
///
/// Letter operators (`is`, `div`, `mod`, ...) are tokenized as atoms, so
/// `TkAtom` names are checked against the operator table too.
fn parse_expr(p : Parser, max_prec : Int) -> Term raise ParseError {
  let mut t = parse_prefix(p)
  for ;; {
    let op = match p.peek() {
      TkSym(s) => s
      TkAtom(s) if infix_op(s) is Some(_) => s
      _ => break
    }
    match infix_op(op) {
      Some((prec, assoc)) if prec <= max_prec => {
        p.advance()
        let rhs_max = if assoc == "xfy" { prec } else { prec - 1 }
        let rhs = parse_expr(p, rhs_max)
        t = Compound(op, [t, rhs])
      }
      _ => break
    }
  }
  t
}

///|
fn parse_prefix(p : Parser) -> Term raise ParseError {
  match p.peek() {
    TkSym(op) =>
      match prefix_op(op) {
        Some(prec) => {
          p.advance()
          Compound(op, [parse_expr(p, prec - 1)])
        }
        _ => parse_primary(p)
      }
    _ => parse_primary(p)
  }
}

///|
fn unexpected(p : Parser) -> ParseError {
  match p.peek() {
    TkEof => ParseError::UnexpectedEof(pos=0)
    _ => ParseError::UnexpectedChar(pos=p.toks[p.pos].pos, ch='?')
  }
}

///|
fn parse_primary(p : Parser) -> Term raise ParseError {
  match p.peek() {
    TkVar(name) => {
      p.advance()
      // `_` is a fresh anonymous variable; other names share one variable
      // per term (see `Parser.vars`).
      if name == "_" {
        variable("_")
      } else {
        match p.vars.get(name) {
          Some(t) => t
          None => {
            let v = variable(name)
            p.vars[name] = v
            v
          }
        }
      }
    }
    TkAtom(name) => {
      p.advance()
      if p.peek() is TkLParen {
        p.advance()
        let args = parse_args(p)
        match p.peek() {
          TkRParen => p.advance()
          _ => raise unexpected(p)
        }
        Compound(name, args)
      } else {
        atom(name)
      }
    }
    TkInt(i) => {
      p.advance()
      Int(i)
    }
    TkFloat(d) => {
      p.advance()
      Float(d)
    }
    TkStr(s) => {
      p.advance()
      str(s)
    }
    TkSym("!") => {
      p.advance()
      atom("!")
    }
    TkLParen => {
      p.advance()
      let t = parse_expr(p, 1200)
      match p.peek() {
        TkRParen => {
          p.advance()
          t
        }
        _ => raise unexpected(p)
      }
    }
    TkLBracket => parse_list(p)
    TkEof => raise ParseError::UnexpectedEof(pos=0)
    _ => raise unexpected(p)
  }
}

///|
/// Parses the comma-separated arguments of a compound term or a list
/// (`,` with precedence 1000 separates, so arguments parse at 999).
fn parse_args(p : Parser) -> Array[Term] raise ParseError {
  let args : Array[Term] = []
  args.push(parse_expr(p, 999))
  for ;; {
    match p.peek() {
      TkSym(",") => {
        p.advance()
        args.push(parse_expr(p, 999))
      }
      _ => break
    }
  }
  args
}

///|
fn parse_list(p : Parser) -> Term raise ParseError {
  p.advance() // consume `[`
  if p.peek() is TkRBracket {
    p.advance()
    return empty_list()
  }
  let elems : Array[Term] = []
  for ;; {
    elems.push(parse_expr(p, 999))
    match p.peek() {
      TkSym(",") => p.advance()
      TkPipe => {
        p.advance()
        let tail = parse_expr(p, 999)
        match p.peek() {
          TkRBracket => p.advance()
          _ => raise unexpected(p)
        }
        return list_tail(elems, tail)
      }
      TkRBracket => {
        p.advance()
        return list(elems)
      }
      TkEof => raise ParseError::UnexpectedEof(pos=0)
      _ => raise unexpected(p)
    }
  }
}

///|
fn expect_eof(p : Parser) -> Unit raise ParseError {
  match p.peek() {
    TkEof => ()
    _ => raise unexpected(p)
  }
}
