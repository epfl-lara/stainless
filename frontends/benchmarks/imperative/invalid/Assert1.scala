/* Copyright 2009-2021 EPFL, Lausanne */

/* Copyright 2009-2021 EPFL, Lausanne */

object Assert1 {

  def foo(): Int = {
    var a = 0
    a += 1
    assert(a == 0)
    a
  }

}
