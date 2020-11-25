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
final class DependencyFinder[S <: IR](s: S) extends Visitor(s) {
  import ir._

  def getFunctions: Set[S#FunDef] = _funs.toSet
  def getClasses: Set[S#ClassDef] = _classes.toSet

  private val _funs = MutableSet[S#FunDef]()
  private val _classes = MutableSet[S#ClassDef]()

  override def visit(fd: FunDef): Unit = _funs += fd
  override def visit(cd: ClassDef): Unit = _classes += cd

}
