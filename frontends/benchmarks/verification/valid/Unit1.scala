/* Copyright 2009-2019 EPFL, Lausanne */

object Unit1 {

  def foo(): Unit = ({
    ()
  }) ensuring(r => true)

}
