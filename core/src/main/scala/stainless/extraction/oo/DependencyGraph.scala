/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._

trait DependencyGraph extends ast.DependencyGraph {
  protected val trees: oo.Trees
  import trees._

  private class ClassCollector extends TreeTraverser {
    var classes: Set[Identifier] = Set.empty

    override def traverse(tpe: Type): Unit = tpe match {
      case ClassType(id, _) =>
        classes += id
        super.traverse(tpe)
      case _ =>
        super.traverse(tpe)
    }

    override def traverse(pat: Pattern): Unit = pat match {
      case ClassPattern(_, ct, _) =>
        classes += ct.id
        super.traverse(pat)

      case _ => super.traverse(pat)
    }

    override def traverse(expr: Expr): Unit = expr match {
      case ClassConstructor(ct, _) =>
        classes += ct.id
        super.traverse(expr)

      case MatchExpr(_, cses) =>
        cses.flatMap { case MatchCase(pat, _, _) =>
          patternOps.collect[Identifier] {
            case ClassPattern(_, ct, _) => Set(ct.id)
            case _ => Set()
          } (pat)
        }.toSet

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
