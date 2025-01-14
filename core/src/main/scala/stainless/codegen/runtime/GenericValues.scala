/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package codegen.runtime

import scala.collection.immutable.{Map => ScalaMap}

object GenericValues {
  private var counter = 0

  private var gvToI = ScalaMap[ast.Trees#GenericValue, Int]()
  private var iTogv = ScalaMap[Int, ast.Trees#GenericValue]()

  def register(gv: ast.Trees#GenericValue): Int = synchronized {
    if (gvToI contains gv) {
      gvToI(gv)
    } else {
      counter += 1
      gvToI += gv -> counter
      iTogv += counter -> gv
      counter
    }
  }

  def get(i: Int): java.lang.Object = synchronized {
    iTogv(i)
  }
}
