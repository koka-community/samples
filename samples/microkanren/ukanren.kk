import std/core/undiv

// Term language
type term
  TEmp
  TPai(car : term, cdr : term)
  TNum(num : int)
  TStr(str : string)
  TSym(sym : string)
  TVar(nm : int)

fun show(t: term): string
  match t
    TEmp -> "()"
    TPai(car, cdr) -> "(" ++ show(car) ++ ", " ++ show(cdr) ++ ")"
    TNum(n) -> n.show
    TStr(s) -> s
    TSym(s) -> s
    TVar(n) -> "var " ++ n.show

fun n(n: int) TNum(n)
fun str(s: string) TStr(s)
fun sym(s: string) TSym(s)
fun v(n: int) TVar(n)
val mk-var = v
val e = TEmp
fun l/p(ls: list<term>)
  match ls
    Nil -> TEmp
    Cons(x, xs) -> TPai(x, p(xs))

val res2 = [1.n, 2.n].p
val res = TPai(TNum(1), TPai(TNum(2), TEmp))

// Define unification
alias subst = list<(int, term)>

effect unify<x>
  final ctl fail(m : string): a
  fun extend(n: int, x: x): ()
  fun canonicalize(t: x): x
  ctl choose(fs: list<f>): f
  fun fresh(): int

fun handle-unify<a>(action: () -> unify<a> (), ?walk: (list<(int, a)>, a) -> a): <div,console> list<list<(int, a)>>
  var subst : some<a> list<(int, a)> := []
  var fresh := 0
  with handler
    final ctl fail(msg)
      println(msg)
      []
    fun canonicalize(x)
      walk(subst, x)
    fun extend(n, x)
      subst := Cons((n, x), subst)
    ctl choose(fs)
      val s' = subst
      fs.map(fn(x) 
        subst := s'
        resume(x)
      ).concat 
    fun fresh()
      fresh := fresh + 1
      fresh
    return(x)
      [subst]
  action()

fun t/(===)(x1: t, x2: t, ?unify: (t, t) -> unify<t> ()): unify<t> ()
  unify(x1.canonicalize, x2.canonicalize)
fun freshvar(?mk-var) mk-var(fresh())
fun disj(fs) choose(fs)()

fun walk(s: subst, t: term): term
  match t
    TVar(n) -> 
      match s.find(fn((n1, _)) -> n == n1)
        Just((_, t1)) -> walk(s, t1.pretend-decreasing)
        Nothing -> t
    _ -> t

fun unify(t0: term, t1: term): unify<term> ()
  match (t0, t1)
    (TNum(n0), TNum(n1)) -> if n1 == n0 then () else fail("Not the same numbers " ++ n0.show ++ " " ++ n1.show)
    (TStr(s0), TStr(s1)) -> if s1 == s0 then () else fail("Not the same strings " ++ s0.show ++ " " ++ s1.show)
    (TSym(s0), TSym(s1)) -> if s1 == s0 then () else fail("Not the same symbols " ++ s0.show ++ " " ++ s1.show)
    (TEmp, TEmp) -> ()
    (TPai(car0, cdr0), TPai(car1, cdr1)) -> 
      unify(car0.pretend-decreasing, car1)
      unify(cdr0.pretend-decreasing, cdr1)
    (TVar(n0), TVar(n1)) -> if n1 == n0 then () else extend(n0, TVar(n1))
    (TVar(n0), t1') -> extend(n0, t1')
    (t0', TVar(n1)) -> extend(n1, t0')
    _ -> fail("Not the same types " ++ show(t0) ++ " " ++ show(t1))

// Write some examples
fun test(x1: term, x2: term, expected: bool): <console,pure> ()
  println("Testing " ++ show(x1) ++ " " ++ show(x2))
  match handle-unify({unify(x1, x2)})
    [] -> 
      if expected then "Failed".println
      else "Success".println
    s -> 
      if expected then 
        ("Success " ++ s.show).println
      else 
        "Failed".println

fun tests()
  test(e, e, True)
  test(1.n, 1.n, True)
  test(e, 1.n, False)
  test(0.v, 42.n, True)
  test([42.n, 0.v].p, [0.v, 35.n].p, False)
  test([0.v, 0.v].p, [42.n, 42.n].p, True)
  test([0.v, 42.n].p, [42.n, 0.v].p, True)
  test([0.v, 42.n].p, [35.n, 0.v].p, False)

  println("Running disj")
  handle-unify
    val x = freshvar()
    val y = freshvar()
    disj([{         
      x === 42.n
      y === 100.n
    }, {
      x === 35.n
    }])
