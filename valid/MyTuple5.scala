/* Copyright 2009-2014 EPFL, Lausanne */

object MyTuple1 {

  abstract class A
  case class B(t: (Int, Int)) extends A
  case class C(a: A) extends A

  def foo(): Int = {
    val t: (Int, (A, Int), Int) = (1, (C(B((4, 5))), 2), 3)
    t match {
      case (_, (B((x, y)), _), _) => x
      case (_, (C(B((_, x))), _), y) => x
      case (_, _, x) => x
    }
  } ensuring( _ == 5)

}
