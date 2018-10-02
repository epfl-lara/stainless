/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._

trait DependencyGraph extends ast.DependencyGraph {
  protected val trees: oo.Trees
  import trees._

  protected class ClassCollector extends Collector with TreeTraverser {
    override def traverse(tpe: Type): Unit = tpe match {
      case ClassType(id, _) =>
        register(id)
        super.traverse(tpe)
      case _ =>
        super.traverse(tpe)
    }

    override def traverse(pat: Pattern): Unit = pat match {
      case ClassPattern(_, ct, _) =>
        register(ct.id)
        super.traverse(pat)
      case _ =>
        super.traverse(pat)
    }

    override def traverse(expr: Expr): Unit = expr match {
      case ClassConstructor(ct, _) =>
        register(ct.id)
        super.traverse(expr)
      case _ =>
        super.traverse(expr)
    }
  }

  protected def getClassCollector: ClassCollector = new ClassCollector

  private def collectClasses(fd: FunDef): Set[Identifier] = {
    val collector = getClassCollector
    collector.traverse(fd)
    collector.result
  }

  private def collectClasses(sort: ADTSort): Set[Identifier] = {
    val collector = getClassCollector
    collector.traverse(sort)
    collector.result
  }

  private def collectClasses(cd: ClassDef): Set[Identifier] = {
    val collector = getClassCollector
    collector.traverse(cd)
    collector.result
  }

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph

    for (fd <- symbols.functions.values; id <- collectClasses(fd)) {
      g += SimpleEdge(fd.id, id)
    }

    for (sort <- symbols.sorts.values; id <- collectClasses(sort)) {
      g += SimpleEdge(sort.id, id)
    }

    for (cd <- symbols.classes.values; id <- collectClasses(cd)) {
      g += SimpleEdge(cd.id, id)
    }

    for (cd <- symbols.classes.values) {
      cd.flags
        .collectFirst { case HasADTInvariant(id) => id }
        .foreach { inv => g += SimpleEdge(cd.id, inv) }

      for (p <- cd.parents) {
        g += SimpleEdge(cd.id, p.id)
      }

      if (cd.flags.contains(IsSealed))
        cd.children(symbols) foreach { dd =>
          g += SimpleEdge(cd.id, dd.id)
        }
    }

    g
  }

}
