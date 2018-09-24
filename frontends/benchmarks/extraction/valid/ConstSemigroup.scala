object ConstSemigroup {

  abstract class Semigroup[M] {
    def append(left: M, right: M): M
  }

  case class Const[A](value: A)

  case class ConstSemigroup[X](x: X) extends Semigroup[Const[X]] {
    def append(left: Const[X], right: Const[X]): Const[X] = Const(x)
  }

  def constSemigroup[X](x: X): Semigroup[Const[X]] = ConstSemigroup[X](x)
}
