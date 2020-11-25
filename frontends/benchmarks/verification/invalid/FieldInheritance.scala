/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object FieldInheritance {

  abstract class Foo[B] {
    val thisIsIt: BigInt = 1
    val weird: B
    def y: BigInt
  }

  case class Bar[X](override val thisIsIt: BigInt, weird: X) extends Foo[X] {
    lazy val y = thisIsIt
  }

  case class Baz[X](weird: X) extends Foo[X] {
    lazy val y = thisIsIt + 1
  }


  def foo[A](f: Foo[A]) = (f.thisIsIt == 1).holds

}
