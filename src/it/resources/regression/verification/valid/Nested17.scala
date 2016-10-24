package test.resources.regression.verification.purescala.valid

/* Copyright 2009-2016 EPFL, Lausanne */

object Nested17 {

  def test(y: Int) = {

    def g() = y

    //this will be in the path condition of h with a function call to g
    val b = g()

    //the tricky part is to capture the free variables of g since the
    //path condition contains a function invocation to g
    def h(): Unit = {
      ()
    } ensuring(res => true)

    h()
  }

}
