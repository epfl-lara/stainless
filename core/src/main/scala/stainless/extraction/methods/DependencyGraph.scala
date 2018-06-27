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

    def invariants: Set[Identifier] = {
      classes flatMap { cid =>
        def isInvariant(fd: FunDef) = fd.flags.contains(IsInvariant) && fd.flags.contains(IsMethodOf(cid))
        symbols.functions.values.find(isInvariant).map(_.id)
      }
    }

    def methods: Set[Identifier] = {
      classes.map(symbols.classes).flatMap(_.methods(symbols))
    }

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
    collector.classes ++ collector.invariants ++ collector.methods // ++ overrides(fd) ++ overriden(fd)
  }

  private def overriden(fd: FunDef): Set[Identifier] = {
    (fd.flags.collectFirst { case IsMethodOf(cid) => cid }) match {
      case None => Set.empty
      case Some(cid) =>
        val cd = symbols.classes(cid)
        if (cd.parents.isEmpty) Set.empty
        else {
          cd.ancestors(symbols).flatMap { tcd =>
            tcd.cd.methods(symbols).filter(_.name == fd.id.name)
          }.toSet
        }
    }
  }

  private def overrides(fd: FunDef): Set[Identifier] = {
    (fd.flags.collectFirst { case IsMethodOf(cid) => cid }) match {
      case None => Set.empty
      case Some(cid) =>
        symbols.classes(cid)
          .descendants(symbols)
          .flatMap(_.methods(symbols))
          .map(symbols.functions)
          .filter(_.id.name == fd.id.name)
          // .filter(_.getType == fd.getType)
          .map(_.id)
          .toSet
    }
  }

  private def collectClasses(cd: ClassDef): Set[Identifier] = {
    val collector = new ClassCollector
    collector.traverse(cd)
    collector.classes ++ collector.invariants
  }

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph
    for ((_, fd) <- symbols.functions; id <- collectClasses(fd)) {
      g += SimpleEdge(fd.id, id)
    }
    for ((_, cd) <- symbols.classes; id <- collectClasses(cd)) {
      g += SimpleEdge(cd.id, id)
    }
    g
  }

}
