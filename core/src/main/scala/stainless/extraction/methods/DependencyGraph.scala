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

  private def collectClasses(cd: ClassDef): Set[Identifier] = {
    val collector = new ClassCollector
    collector.traverse(cd)
    collector.classes
  }


  // Add an edge between a node `n` and an override `oid` of a function `fd` if
  // `n` has transitive edges to `fd` and transitive edges to `cid`, the class of `oid`
  protected def addEdgesToOverrides(g: DiGraph[Identifier, SimpleEdge[Identifier]]) = {
    var res = g
    for (fd <- symbols.functions.values) {
      for (oid <- overrides(fd)) {
        symbols.functions(oid).flags.collectFirst {
          case IsMethodOf(cid) =>
            // we look at transitive edges in `res` rather than in `g` in 
            // order to take into account newly added edges
            for (n <- res.transitivePred(fd.id) & res.transitivePred(cid)) {
              res += SimpleEdge(n, oid)
            }
        }
      }
    }
    res
  }

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph

    for (fd <- symbols.functions.values; id <- collectClasses(fd)) {
      g += SimpleEdge(fd.id, id)
    }

    for (cd <- symbols.classes.values; id <- collectClasses(cd)) {
      g += SimpleEdge(cd.id, id)
    }

    for (cd <- symbols.classes.values) {
      invariant(cd) foreach { inv => g += SimpleEdge(cd.id, inv) }
    }

    inox.utils.fixpoint(addEdgesToOverrides)(g)
  }

  private def invariant(cd: ClassDef): Option[Identifier] = {
    def isInvariant(fd: FunDef) = fd.flags.contains(IsInvariant) && fd.flags.contains(IsMethodOf(cd.id))
    symbols.functions.values.find(isInvariant).map(_.id)
  }

  private def overrides(fd: FunDef): Set[Identifier] = {
    if (!fd.id.isInstanceOf[SymbolIdentifier]) return Set.empty

    val symbol = fd.id.asInstanceOf[SymbolIdentifier].symbol

    (fd.flags.collectFirst { case IsMethodOf(cid) => cid }) match {
      case None => Set.empty
      case Some(cid) =>
        symbols.classes(cid)
          .descendants(symbols)
          .flatMap(_.methods(symbols))
          .filter(_.symbol == symbol)
          .toSet
    }
  }


}
