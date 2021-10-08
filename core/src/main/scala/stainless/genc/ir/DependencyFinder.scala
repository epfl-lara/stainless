/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import scala.collection.mutable.{ Set => MutableSet }

/*
 * Compute the dependencies of a program; that is, the set of functions and classes involved.
 *
 * NOTE Don't reuse an instance of this DependencyFinder on multiple trees!
 */
final class DependencyFinder[S <: IR](override val ir: S) extends Visitor(ir) {
  import ir._

  def getFunctions: Set[ir.FunDef] = _funs.toSet
  def getClasses: Set[ir.ClassDef] = _classes.toSet

  private val _funs = MutableSet[ir.FunDef]()
  private val _classes = MutableSet[ir.ClassDef]()

  override def visit(fd: FunDef): Unit = _funs += fd
  override def visit(cd: ClassDef): Unit = _classes += cd

}
