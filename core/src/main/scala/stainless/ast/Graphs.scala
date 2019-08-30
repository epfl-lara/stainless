/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import inox.utils.Graphs._

trait CallGraph extends inox.ast.CallGraph {
  protected val trees: Trees
  import trees._

  protected trait FunctionCollector extends SelfTreeTraverser with super.FunctionCollector {
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

  override protected def getFunctionCollector = new FunctionCollector {}
}

trait DependencyGraph extends inox.ast.DependencyGraph with CallGraph {
  import trees._

  protected trait SortCollector extends SelfTreeTraverser with super.SortCollector {
    override def traverse(pat: Pattern): Unit = pat match {
      case ADTPattern(_, id, _, _) =>
        register(symbols.getConstructor(id).sort)
        super.traverse(pat)
      case _ =>
        super.traverse(pat)
    }

    override def traverse(tpe: Type): Unit = tpe match {
      case RecursiveType(id, _, _) =>
        register(id)
        super.traverse(tpe)
      case _ =>
        super.traverse(tpe)
    }

    override def traverse(expr: Expr): Unit = expr match {
      case SizedADT(id, _, _, _) =>
        register(symbols.getConstructor(id).sort)
        super.traverse(expr)
      case _ =>
        super.traverse(expr)
    }
  }

  override def getSortCollector = new SortCollector {}
}
