/*----------------------------------------------------------------------------
   Copyright 2024, Koka-Community Authors

   Licensed under the MIT License ("The License"). You may not
   use this file except in compliance with the License. A copy of the License
   can be found in the LICENSE file at the root of this distribution.
----------------------------------------------------------------------------*/
module tagless


value struct id<a>
   v: a

struct applicative<t>
   pure: forall<v> v -> t<v>
   fmap: forall<a,b> (t<a>, (a -> b)) -> t<b>
   ap: forall<a,b> (t<a>, t<(a -> b)>) -> t<b>

struct app2<t>
   pure: forall<v> v -> t<v>
   fmap: forall<a,b> (t<a>, (a -> b)) -> t<b>
   fmap2: forall<a,b,c> (t<a>, t<b>, ((a, b) -> c)) -> t<c>
   ap: forall<a,b> (t<a>, t<(a -> b)>) -> t<b>
   ap2: forall<a,b,c> (t<a>, t<b>, t<(a, b) -> c>) -> t<c>

val id/pure = fn(x) Id(x)
val id/fmap = fn(x,f) Id(f(x.v))
val id/fmap2 = fn(x,y,f) Id(f(x.v, y.v))
val id/ap = fn(x,f) Id(f.v.(x.v))
val id/ap2 = fn(x,y,f) Id(f.v.(x.v, y.v))
val id/applicative = Applicative(pure, fmap, ap)
val id/app2 = App2(pure, fmap, fmap2, ap, ap2)

struct ssym<r>
   int: int -> r<int>
   add: r<(int -> (int -> int))>
   mul: r<(int -> (int -> int))>
   app: forall<a,b> (r<(a -> b)>) -> (r<a> -> r<b>);

struct lam<r>
   lam: forall<a,b> (r<a> -> r<b>) -> r<a -> b>

fun basic/int(i: int): id<int>
   Id(i)
val basic/add = Id(fn (a) fn (b: int) a + b)
val basic/mul = Id(fn (a) fn (b: int) a * b)
val basic/app = fn(f) fn(x) Id(f.v.(x.v))
val basic/ssym = Ssym(basic/int, basic/add, basic/mul, basic/app)
val basic/lampure = Lam(fn(f) Id(fn(x) f(Id(x)).v))

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

fun reified/int(i: int)
   Reified(fn(_) LitE(i))
val reified/add = Reified(fn(_) AddE)
val reified/mul = Reified(fn(_) MulE)
val reified/app = fn(f) fn(x) Reified(fn(c) AppE(f.unC.(c), x.unC.(c)))
val reified/lampure = Lam(fn(f) Reified(fn(c)
         val n = "x_" ++ c.show
         val body = f(Reified(fn(_) VarE(n))).unC()(c + 1)
         LamE(n, body)
      ))

val reified/ssym = Ssym(reified/int, reified/add, reified/mul, reified/app)

pub inline fun tagless/apx(f: m<r<a -> b>>, x: m<r<a>>, ?ssym: ssym<r>, .?applicative: applicative<m>): m<r<b>>
   x.ap(f.fmap(?ssym.app))

// pub inline fun tagless/ap2(f: m<r<(a, b) -> c>>, x: m<r<a>>, ?ssym: ssym<r>, .?applicative: applicative<m>): m<r<b>>
//    x.ap(f.fmap(?ssym.app))

// Generic definitions
pub inline fun tagless/int(i: int, ?ssym: ssym<r>, .?applicative: applicative<m>): m<r<int>>
   pure(?ssym.int.(i))

pub inline fun tagless/(+)(i1: m<r<int>>, i2: m<r<int>>, ?ssym: ssym<r>, .?applicative: applicative<m>): m<r<int>>
   pure(?ssym.add).apx(i1).apx(i2)

pub inline fun tagless/(*)(i1: m<r<int>>, i2: m<r<int>>, ?ssym: ssym<r>, .?applicative: applicative<m>): m<r<int>>
   pure(?ssym.mul).apx(i1).apx(i2)

fun example(ssym)
   val res = 1.tagless/int + 2.int
   res.v

pub fun test()
   val res = example(basic/ssym)
   res.v.show.println
   val res2 = example(reified/ssym)
   res2.unC.(0).show.println

   ()
  