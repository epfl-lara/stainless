/* Copyright 2009-2016 EPFL, Lausanne */

object MyTuple1 {

  def foo(): BigInt = {
    val t = (BigInt(1), true, BigInt(3))
    val a1 = t._1
    val a2 = t._2
    val a3 = t._3
    a3
  } ensuring( _ == 3)

}
