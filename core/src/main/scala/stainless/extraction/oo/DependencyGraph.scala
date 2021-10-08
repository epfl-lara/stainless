/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._

trait DependencyGraph extends ast.DependencyGraph { self =>
  protected val trees: oo.Trees
  import trees._

  // We first extend TreeTraverser and then Collector, otherwise we get the following error:
  //
  //   cannot override final member:
  //      final override def traverse(e: Expr, env: Env): Unit (defined in trait TreeTraverser)
  //      with  override def traverse(e: Expr, env: Env): Unit (defined in trait Traverser)
  //
  protected class ClassCollector(override val trees: self.trees.type)
    extends TreeTraverser with Collector {

    def this() = this(self.trees)

    def traverseDef(defn: Definition): Unit = defn match {
      case as: ADTSort => traverse(as)
      case fd: FunDef => traverse(fd)
      case cd: ClassDef => traverse(cd)
      case td: TypeDef => traverse(td)
    }

    override def traverse(tpe: Type): Unit = tpe match {
      case ClassType(id, _) =>
        register(id)
        super.traverse(tpe)
      case TypeSelect(_, id) =>
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

  private def collectAll(defn: Definition): Set[Identifier] = {
    val collector = getClassCollector
    collector.traverseDef(defn)
    collector.result
  }

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph

    for (fd <- symbols.functions.values; id <- collectAll(fd)) {
      g += SimpleEdge(fd.id, id)
    }

    for (sort <- symbols.sorts.values; id <- collectAll(sort)) {
      g += SimpleEdge(sort.id, id)
    }

    for (cd <- symbols.classes.values; id <- collectAll(cd)) {
      g += SimpleEdge(cd.id, id)
    }

    for (td <- symbols.typeDefs.values; id <- collectAll(td)) {
      g += SimpleEdge(td.id, id)
    }

    for (cd <- symbols.classes.values) {
      cd.flags
        .collectFirst { case HasADTInvariant(id) => id }
        .foreach { inv => g += SimpleEdge(cd.id, inv) }

      for (p <- cd.parents) {
        g += SimpleEdge(cd.id, p.id)
      }

      if (cd.flags.contains(IsSealed))
        cd.children(using symbols) foreach { dd =>
          g += SimpleEdge(cd.id, dd.id)
        }
    }

    g
  }

}
