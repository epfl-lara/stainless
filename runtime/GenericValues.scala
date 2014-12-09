/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package codegen.runtime

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees.{Tuple => LeonTuple, _}
import purescala.TreeOps.valuateWithModel
import purescala.TypeTrees._

import scala.collection.immutable.{Map => ScalaMap}

import synthesis._

object GenericValues {
  private[this] var counter = 0;

  private[this] var gvToI = ScalaMap[GenericValue, Int]()
  private[this] var iTogv = ScalaMap[Int, GenericValue]()

  def register(gv: GenericValue): Int = {
    if (gvToI contains gv) {
      gvToI(gv)
    } else {
      counter += 1;
      gvToI += gv -> counter
      iTogv += counter -> gv
      counter
    }
  }

  def get(i: Int): java.lang.Object = {
    iTogv(i)
  }
}
