import stainless.lang._

object NonUniformRecursion {
  sealed abstract class Exp[A]
  case class Var[A](a: A) extends Exp[A]
  case class Lam[A](body: Exp[Var[A]]) extends Exp[A]

  case class Nest[A](a: A, next: Option[Nest[(A, A)]])

  // Recursive occurrences with type parameters or ground types are fine
  case class Swap[A, B](a: A, rest: Option[Swap[B, A]], ints: Option[Swap[BigInt, BigInt]])

  // Member classes implicitly take the type arguments of their enclosing classes
  trait Lang[V] {
    abstract class Expr
  }
  trait ListLang[W] extends Lang[List[W]] {
    case class Cons(h: W, t: Expr) extends Expr
  }
}
