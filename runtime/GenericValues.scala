/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package codegen.runtime

import purescala.Trees.GenericValue
import scala.collection.immutable.{Map => ScalaMap}

object GenericValues {
  private[this] var counter = 0

  private[this] var gvToI = ScalaMap[GenericValue, Int]()
  private[this] var iTogv = ScalaMap[Int, GenericValue]()

  def register(gv: GenericValue): Int = {
    if (gvToI contains gv) {
      gvToI(gv)
    } else {
      counter += 1
      gvToI += gv -> counter
      iTogv += counter -> gv
      counter
    }
  }

  def get(i: Int): java.lang.Object = {
    iTogv(i)
  }
}
