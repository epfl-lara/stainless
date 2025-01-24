package stainless.lang
import stainless.annotation.*

@library
object Quantifiers {
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

  @ghost @opaque
  def Exists[T](p : T => Boolean): Boolean =
    !Forall((x:T) => !p(x))

  @ghost @extern 
  def ExistsThe[T](w: T)(p: T => Boolean): Unit = {
    require(p(w))
    (??? : Unit)
  }.ensuring(_ => Exists(p))

  @ghost @extern 
  def pickWitness[T](p: T => Boolean): T = {
    require(Exists(p))
    (??? : T)
  }.ensuring(p)

  @ghost @extern
  def notExists[T](p: T => Boolean): Unit = {
    require(!Exists(p))
    ()
  }.ensuring(_ => Forall((x:T) => !p(x)))

  @ghost @extern
  def notExistsNot[T](p: T => Boolean): Unit = {
    require(!Exists((x:T) => !p(x)))
    ()
  }.ensuring(_ => Forall(p))

  @ghost @extern 
  def notForall[T](p: T => Boolean): Unit = {
    require(!Forall(p))
    ()
  }.ensuring(_ => Exists((x:T) => !p(x)))
}
