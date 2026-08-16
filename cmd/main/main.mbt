///|
/// Demo: a small family database plus list programming, evaluated by the
/// Prolog EDSL. The program is written in plain Prolog syntax and parsed
/// with `parse_program`.
///
/// Run with `moon run cmd/main`.
using @prolog {parse_program, parse_term}

///|
fn main raise {
  let family_src =
    #|parent(john, mary). parent(john, jane). parent(mary, bob).
    #|ancestor(X, Y) :- parent(X, Y).
    #|ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
    #|
  let prog = parse_program(family_src)
  println("== family ==")
  for ans in prog.solve([parse_term("parent(X, _)")]) {
    println(ans)
  }
  println("ancestors of bob:")
  for ans in prog.solve([parse_term("ancestor(Y, bob)")]) {
    println(ans)
  }

  println("== lists ==")
  let lib_src =
    #|member(X, [X | _]).
    #|member(X, [_ | T]) :- member(X, T).
    #|append([], L, L).
    #|append([H | T], L, [H | R]) :- append(T, L, R).
    #|reverse([], []).
    #|reverse([H | T], R) :- reverse(T, R1), append(R1, [H], R).
    #|
  let lib = parse_program(lib_src)
  for ans in lib.solve([parse_term("member(E, [1, 2, 3])")]) {
    println(ans)
  }
  for ans in lib.solve([parse_term("append([1, 2], [3, 4], XS)")]) {
    println(ans)
  }
  for ans in lib.solve([parse_term("reverse([1, 2, 3], R)")]) {
    println(ans)
  }
  println("== meta ==")
  for ans in lib.solve([parse_term("findall(X, member(X, [1, 2, 3]), L)")]) {
    println(ans)
  }
  for ans in lib.solve([parse_term("(member(X, [1, 2, 3]) -> X = 9 ; X = 0)")]) {
    println(ans)
  }
  for ans in lib.solve([parse_term("(fail -> X = 9 ; X = 0)")]) {
    println(ans)
  }
  for ans in lib.solve([parse_term("sort([3, 1, 2, 1], S)")]) {
    println(ans)
  }

  println("== DCG ==")
  let grammar_src =
    #|digits([D]) --> [D].
    #|digits([D | Ds]) --> [D], digits(Ds).
    #|
  let grammar = parse_program(grammar_src)
  for ans in grammar.solve([parse_term("phrase(digits(Ds), [1, 2, 3])")]) {
    println(ans)
  }

  println("== dif ==")
  for ans in lib.solve([parse_term("(dif(X, b), X = a)")]) {
    println(ans)
  }
  let none = lib.solve([parse_term("(dif(X, b), X = b)")]).to_array()
  println("dif(X, b), X = b has \{none.length()} solution(s)")

  println("== dynamic predicates ==")
  let dyn_prog = parse_program(":- dynamic(fact/2).")
  for ans in dyn_prog.solve([parse_term("assertz(fact(john, 42))")]) {
    println(ans)
  }
  for ans in dyn_prog.solve([parse_term("assertz(fact(mary, 7))")]) {
    println(ans)
  }
  for ans in dyn_prog.solve([parse_term("fact(X, N)")]) {
    println(ans)
  }
  for
    ans in dyn_prog.solve([
      parse_term("(fact(john, N), retract(fact(john, N)))"),
    ]) {
    println(ans)
  }
  println("facts left: \{dyn_prog.solve([parse_term("fact(_, _)")]).count()}")
}
