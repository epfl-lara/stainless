/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import inox.utils.Graphs._

trait CallGraph extends ast.CallGraph {
  protected val trees: methods.Trees
  import trees._

  private def collectCalls(e: Expr): Set[Identifier] = exprOps.collect[Identifier] {
    case MethodInvocation(_, id, _, _) => Set(id)
    case _ => Set()
  } (e)

  override protected def computeCallGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeCallGraph
    for ((_, fd) <- symbols.functions; id <- collectCalls(fd.fullBody)) {
      g += SimpleEdge(fd.id, id)
    }
    g
  }
}

trait DependencyGraph extends ast.DependencyGraph with CallGraph {
  import trees._

  private class ClassCollector extends TreeTraverser {
    var classes: Set[Identifier] = Set.empty

    override def traverse(flag: Flag): Unit = flag match {
      case IsMethodOf(id) =>
        classes += id
        super.traverse(flag)

      case _ => super.traverse(flag)
    }

    override def traverse(expr: Expr): Unit = expr match {
      case This(ct) =>
        classes += ct.id
        super.traverse(expr)

      case Super(ct) =>
        classes += ct.id
        super.traverse(expr)

      case _ =>
        super.traverse(expr)
    }
  }

  private def collectClasses(fd: FunDef): Set[Identifier] = {
    val collector = new ClassCollector
    collector.traverse(fd)
    collector.classes
  }

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph
    for ((_, fd) <- symbols.functions; id <- collectClasses(fd)) {
      g += SimpleEdge(fd.id, id)
    }
    g
  }

}
