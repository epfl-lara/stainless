/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

import inox.utils.Graphs._

trait CallGraph extends ast.CallGraph {
  protected val trees: methods.Trees
  import trees._

  protected class MethodsFunctionCollector extends ConcreteStainlessFunctionCollector with OOSelfTreeTraverser {

    override def traverse(e: Expr): Unit = e match {
      case MethodInvocation(_, id, _, _) =>
        register(id)
        super.traverse(e)
      case _ =>
        super.traverse(e)
    }
  }

  override protected def getFunctionCollector = new MethodsFunctionCollector
}

trait DependencyGraph extends oo.DependencyGraph with CallGraph {
  import trees._
  import symbols.given

  protected class MethodsClassCollector extends ClassCollector(trees) with OOSelfTreeTraverser {
    override def traverse(flag: Flag): Unit = flag match {
      case IsMethodOf(id) =>
        register(id)
        super.traverse(flag)
      case _ =>
        super.traverse(flag)
    }

    override def traverse(expr: Expr): Unit = expr match {
      case This(ct) =>
        register(ct.id)
        super.traverse(expr)
      case Super(ct) =>
        register(ct.id)
        super.traverse(expr)
      case _ =>
        super.traverse(expr)
    }
  }

  override protected def getClassCollector: ClassCollector = new MethodsClassCollector

  // Add an edge between a node `n` and an override `oid` of a function `fd` if
  // `n` has transitive edges to `fd` and transitive edges to `cid`, the class of `oid`
  protected def addEdgesToOverrides(g: DiGraph[Identifier, SimpleEdge[Identifier]]) = {
    var res = g
    for (fd <- symbols.functions.values) {
      for (oid <- overrides(fd)) {
        symbols.getFunction(oid).flags.collectFirst {
          case IsMethodOf(cid) =>
            // we look at transitive edges in `res` rather than in `g` in 
            // order to take into account newly added edges
            for (n <- (res.transitivePred(fd.id) + fd.id) & (res.transitivePred(cid) + cid)) {
              res += SimpleEdge(n, oid)
            }
        }
      }
    }
    res
  }

  private def laws(cd: ClassDef): Set[Identifier] = {
    (cd +: cd.ancestors.map(_.cd)).reverse.foldLeft(Map[Symbol, Identifier]()) {
      case (laws, cd) =>
        val methods = cd.methods
        val newLaws = methods
          .filter(id => symbols.getFunction(id).flags.exists(_.name == "law"))
          .map(id => id.symbol -> id)
        laws -- methods.map(_.symbol) ++ newLaws
    }.values.toSet
  }

  private def overrides(fd: FunDef): Set[Identifier] = {
    if (!fd.id.isInstanceOf[SymbolIdentifier]) return Set.empty

    val symbol = fd.id.asInstanceOf[SymbolIdentifier].symbol

    (fd.flags.collectFirst { case IsMethodOf(cid) => cid }) match {
      case None => Set.empty
      case Some(cid) =>
        def rec(cd: ClassDef): Set[Identifier] = cd.children(using symbols).flatMap {
          cd => cd.methods.find(_.symbol == symbol) match {
            case Some(id) => Set(id: Identifier)
            case None => rec(cd)
          }
        }.toSet

        rec(symbols.getClass(cid))
    }
  }

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph

    for (cd <- symbols.classes.values) {
      cd.invariant foreach { inv => g += SimpleEdge(cd.id, inv.id) }
      symbols.paramInits(cd.id) foreach { paramInit => g += SimpleEdge(cd.id, paramInit.id) }

      if (!(cd.flags contains IsAbstract)) {
        laws(cd) foreach { law => g += SimpleEdge(law, cd.id) }
      }

      for (fid <- cd.methods if symbols.getFunction(fid).isAccessor) {
        g += SimpleEdge(cd.id, fid)
      }
    }

    for (fd <- symbols.functions.values; id <- overrides(fd)) {
      g += SimpleEdge(id, fd.id)
    }

    inox.utils.fixpoint(addEdgesToOverrides)(g)
  }
}
