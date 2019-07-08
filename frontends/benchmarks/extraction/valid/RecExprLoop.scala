sealed abstract class Exp[A]
case class Var[A](a: A) extends Exp[A]
case class Lam[A](body: Exp[Var[A]]) extends Exp[A]
