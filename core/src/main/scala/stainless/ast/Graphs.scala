/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import inox.utils.Graphs._

trait CallGraph extends inox.ast.CallGraph {
  protected val trees: Trees
  import trees._

  private def collectCalls(e: Expr): Set[Identifier] = exprOps.collect[Identifier] {
    case MatchExpr(_, cses) =>
      cses.flatMap { case MatchCase(pat, _, _) =>
        patternOps.collect[Identifier] {
          case UnapplyPattern(_, _, id, _, _) => Set(id)
          case _ => Set()
        } (pat)
      }.toSet
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

trait DependencyGraph extends inox.ast.DependencyGraph with CallGraph {
  import trees._

  private def collectSorts(e: Expr): Set[Identifier] = exprOps.collect[Identifier] {
    case MatchExpr(_, cses) =>
      cses.flatMap { case MatchCase(pat, _, _) =>
        patternOps.collect[Identifier] {
          case ADTPattern(_, id, _, _) => Set(id)
          case _ => Set()
        } (pat)
      }.toSet
    case _ => Set()
  } (e)

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph
    for ((_, fd) <- symbols.functions; id <- collectSorts(fd.fullBody)) {
      g += SimpleEdge(fd.id, id)
    }
    g
  }
}
