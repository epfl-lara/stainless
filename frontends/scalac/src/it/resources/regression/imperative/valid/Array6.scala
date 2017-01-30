/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Array6 {

  def test(): Int = {
    var c = 1
    val a = Array(0,1,2,3)
    a({
      if(a(0) == 0) { c = c+1; 1}
      else { c = c+2; 2}
    }) = { c = c*2; -1}
    c
  } ensuring(res => res == 4)

}
