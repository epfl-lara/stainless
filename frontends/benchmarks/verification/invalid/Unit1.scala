/* Copyright 2009-2021 EPFL, Lausanne */

object Unit1 {

  def foo(u: Unit): Unit = ({
    u
  }) ensuring(res => false)

}
