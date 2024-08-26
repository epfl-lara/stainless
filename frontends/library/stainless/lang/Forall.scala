package stainless.lang
import stainless.annotation.*
import stainless.lang.*
object Forall {
  // Forall is opaque forall with (numbers in name instead of overloading)
  @ghost @opaque @library
  def Forall[A](p: A => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall2[A,B](p: (A,B) => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall3[A,B,C](p: (A,B,C) => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall4[A,B,C,D](p: (A,B,C,D) => Boolean): Boolean = forall(p)
  @ghost @opaque @library
  def Forall5[A,B,C,D,E](p: (A,B,C,D,E) => Boolean): Boolean = forall(p)

  // We instantiate it explicitly.
  @ghost @opaque @library
  def ForallOf[A](p: A => Boolean)(a: A): Unit = {
    require(Forall(p))
    unfold(Forall(p))
  }.ensuring(_ => p(a))

  // Predicates of larger arity
  @ghost @opaque @library
  def Forall2of[A,B](p: (A,B) => Boolean)(a: A, b: B): Unit = {
    require(Forall2(p))
    unfold(Forall2(p))
  }.ensuring(_ => p(a,b))
  @ghost @opaque @library
  def Forall3of[A,B,C](p: (A,B,C) => Boolean)(a: A, b: B, c: C): Unit = {
    require(Forall3(p))
    unfold(Forall3(p))
  }.ensuring(_ => p(a,b,c))
  @ghost @opaque @library
  def Forall4of[A,B,C,D](p: (A,B,C,D) => Boolean)(a: A, b: B, c: C, d: D): Unit = {
    require(Forall4(p))
    unfold(Forall4(p))
  }.ensuring(_ => p(a,b,c,d))
  @ghost @opaque @library
  def Forall5of[A,B,C,D,E](p: (A,B,C,D,E) => Boolean)(a: A, b: B, c: C, d: D, e: E): Unit = {
    require(Forall5(p))
    unfold(Forall5(p))
  }.ensuring(_ => p(a,b,c,d,e))

}
