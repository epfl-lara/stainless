/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import inox.utils.Graphs._

trait CallGraph extends inox.ast.CallGraph {
  protected val trees: Trees
  import trees._

  protected class FunctionCollector extends super.FunctionCollector with TreeTraverser {
    override def traverse(pat: Pattern): Unit = pat match {
      case UnapplyPattern(_, _, id, _, _) =>
        register(id)
        super.traverse(pat)
      case _ =>
        super.traverse(pat)
    }

    override def traverse(flag: Flag): Unit = flag match {
      case IsUnapply(isEmpty, get) =>
        register(isEmpty)
        register(get)
        super.traverse(flag)
      case _ =>
        super.traverse(flag)
    }
  }

  override protected def getFunctionCollector = new FunctionCollector
}

trait DependencyGraph extends inox.ast.DependencyGraph with CallGraph {
  import trees._

  protected class SortCollector extends super.SortCollector with TreeTraverser {
    override def traverse(pat: Pattern): Unit = pat match {
      case ADTPattern(_, id, _, _) =>
        register(symbols.getConstructor(id).sort)
        super.traverse(pat)
      case _ =>
        super.traverse(pat)
    }
  }

  override protected def getSortCollector = new SortCollector
}

