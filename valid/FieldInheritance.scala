/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object FieldInheritance {

  abstract class Foo[B] {
    val thisIsIt: BigInt = 1
    val y: BigInt
    val weird: B
  }

  case class Bar[X](override val thisIsIt: BigInt, weird: X) extends Foo[X] {
    val y = thisIsIt
  }
  
  case class Baz[X](weird: X) extends Foo[X] {
    val y = thisIsIt + 1
  }


  def foo[A](f: Foo[A]) = { f match {
    case Bar(t, _) => f.thisIsIt == t
    case _ => true
  }}.holds

}
