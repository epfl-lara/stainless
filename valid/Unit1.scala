/* Copyright 2009-2016 EPFL, Lausanne */

object Unit1 {

  def foo(): Unit = ({
    ()
  }) ensuring(r => true)

}
