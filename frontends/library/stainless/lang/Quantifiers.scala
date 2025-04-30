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

  // Functions relationships

  // To see an example of its use, see frontends/benchmarks/verification/valid/ForallExistsBijection.scala

  // Needs to be inlined, otherwise we would need to be able to unfold twice to 
  // make the forall (lowercase) visible
  // But by doing so, we then lose the relationship between this inlined body and the "function" given as invariant
  // in the class below. So we need both the body (inline def) and a function
  @ghost
  inline def semiInverseBody[A, B](f: A => B, g: B => A): Boolean = Forall((b: B) => f(g(b)) == b)

  @ghost
  def semiInverse[A, B](f: A => B, g: B => A): Boolean = semiInverseBody(f, g)
  case class Bijection[A, B](f: A => B, g: B => A):
    StaticChecks.require(semiInverse(f, g))
    StaticChecks.require(semiInverse(g, f))
  end Bijection


  @ghost inline def semiPartialInverseBody[A, B](f: A => Option[B], g: B => Option[A]): Boolean = Forall((b: B) => g(b) match {
    case Some(a) => f(a) match {
      case Some(b2) => b == b2
      case _ => true
    }
    case _ => true
  }) 

  @ghost def semiPartialInverse[A, B](f: A => Option[B], g: B => Option[A]): Boolean = semiPartialInverseBody(f, g)

  case class PartialBijection[A, B](f: A => Option[B], g: B => Option[A]):
    StaticChecks.require(semiPartialInverse(f, g))
    StaticChecks.require(semiPartialInverse(g, f))
  end PartialBijection
  
  case class Injection[A, B](f: A => B, g: B => A):
    StaticChecks.require(semiInverse(g, f)) // g(f(a)) == a
  end Injection


  
  
}
