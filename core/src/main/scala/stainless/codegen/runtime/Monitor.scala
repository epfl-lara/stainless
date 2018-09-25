/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package codegen.runtime

abstract class Monitor {
  def onInvocation(): Unit

  def typeParams(params: Array[Int], tps: Array[Int], newTps: Array[Int]): Array[Int]

  def typeSubstitute(id: Int, closures: Array[AnyRef]): Int

  def onChooseInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): AnyRef

  def onForallInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): Boolean
}

