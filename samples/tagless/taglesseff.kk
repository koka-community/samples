/*----------------------------------------------------------------------------
   Copyright 2024, Koka-Community Authors

   Licensed under the MIT License ("The License"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/
module taglesseff

struct ssym<r,e>
   intV: int -> e r<int>
   add: r<(int, int) -> e int>
   mul: r<(int, int) -> e int>
   app: forall<a,b> (r<(a -> e b)>, r<a>) -> e r<b>;
   app2: forall<a,b,c> (r<((a, b) -> e c)>, r<a>, r<b>) -> e r<c>;

struct lam<r,e>
   lam: forall<a,b> (r<a> -> e r<b>) -> r<a -> e b>;

struct id<a>
   v: a

val basic/intV = fn(i: int) Id(i)
val basic/add = Id(fn(a, b: int) a + b)
val basic/mul = Id(fn(a, b: int) a * b)
val basic/app = fn(f, x) Id(f.v.(x.v))
val basic/app2 = fn(f, x, y) Id(f.v.(x.v, y.v))
val basic/ssym = Ssym(basic/intV, basic/add, basic/mul, basic/app, basic/app2)
// val basic/lampure = Lam(fn(f) ) 

type exp
   LitE(i: int)
   VarE(x : string)
   AddE
   MulE
   AppE(f: exp, x: exp)
   LamE(s : string, b: exp)

fun show(e: exp): string
   match e
      LitE(i) -> i.show
      VarE(x) -> x
      AddE -> "Add"
      MulE -> "Mul"
      AppE(AppE(AddE, x), y) -> x.show ++ " + " ++ y.show
      AppE(AppE(MulE, x), y) -> x.show ++ " * " ++ y.show 
      AppE(f, e) -> f.show ++ "(" ++ e.show ++ ")"
      LamE(x, b) -> "λ" ++ x ++ "." ++ b.show

struct reified<a> 
   unC: int -> exp

fun reified/intV(i: int)
   Reified(fn(_) LitE(i))
val reified/add = Reified(fn(_) AddE)
val reified/mul = Reified(fn(_) MulE)
val reified/app = fn(f, x) Reified(fn(c) AppE(f.unC.(c), x.unC.(c)))
val reified/app2 = fn(f, x, y) Reified(fn(c) AppE(AppE(f.unC.(c), x.unC.(c)), y.unC.(c)))
val reified/lampure = Lam(fn(f) Reified(fn(c)
         val n = "x_" ++ c.show
         val body = f(Reified(fn(_) VarE(n))).unC()(c + 1)
         LamE(n, body)
      ))

val reified/ssym = Ssym(reified/intV, reified/add, reified/mul, reified/app, reified/app2)

// Generic definitions
pub inline fun tagless/int(i: int, ?ssym: ssym<r,e>): e r<int>
   ?ssym.intV.(i)

pub inline fun tagless/(+)(i1: r<int>, i2: r<int>, .?ssym: ssym<r,e>): e r<int>
   app2(add, i1, i2)

pub inline fun tagless/(*)(i1: r<int>, i2: r<int>, .?ssym: ssym<r,e>): e r<int>
   app2(mul, i1, i2)

pub inline fun lam(f : r<a> -> e r<b>, .?lam: lam<r,e>): r<a -> e b>
   lam(f)

effect reader<r,a>
   fun get(): r<a>


fun example(ssym)
   val res = 1.int + 2.int
   res

pub fun test()
   val res = example(basic/ssym)
   res.v.show.println
   val res2 = example(reified/ssym)
   res2.unC.(0).show.println

   ()
  