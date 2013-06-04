/* Copyright 2009-2013 EPFL, Lausanne */

object Unit1 {

  def foo(): Unit = ({
    ()
  }) ensuring(r => true)

}
