import stainless.lang._

object FieldInheritance2 {

  sealed abstract class Foo[B] {
    val thisIsIt: BigInt = 1
    val y: BigInt
    val z: BigInt = y
  }

  case class Bar[X](override val thisIsIt: BigInt) extends Foo[X] {
    val y = thisIsIt
  }

  def foo[A](f: Foo[A]) = {  f.y == f.z }.holds // wrong because f.z is always null
}
