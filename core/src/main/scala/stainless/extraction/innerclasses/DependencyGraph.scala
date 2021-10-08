/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

import inox.utils.Graphs._

trait DependencyGraph extends methods.DependencyGraph {
  protected val trees: innerclasses.Trees
  import trees._
  import symbols.given

  protected class LocalClassCollector extends ClassCollector(trees) with OOSelfTreeTraverser {

    var localClasses: Set[LocalClassDef] = Set.empty

    def traverse(lmd: LocalMethodDef): Unit = traverse(lmd.toFunDef)

    override def traverse(expr: Expr): Unit = expr match {
      case FunctionInvocation(id, _, _) =>
        register(id)
        super.traverse(expr)

      case MethodInvocation(_, id, _, _) =>
        register(id)
        super.traverse(expr)

      case LetClass(lcds, body) =>
        localClasses = localClasses ++ lcds.toSet

        lcds foreach (_.parents foreach traverse)
        lcds foreach (_.methods foreach traverse)
        lcds foreach (_.fields foreach traverse)
        traverse(body)

      case LocalClassConstructor(lct: LocalClassType, args) =>
        lct.ancestors foreach traverse
        lct.tps foreach traverse
        args foreach traverse

      case LocalClassSelector(expr, _, tpe) =>
        traverse(expr)
        traverse(tpe)

      case LocalMethodInvocation(receiver, _, _, tps, args) =>
        traverse(receiver)
        tps foreach traverse
        args foreach traverse

      case _ =>
        super.traverse(expr)
    }
  }

  private def collectClasses(fd: FunDef): (Set[Identifier], Set[LocalClassDef]) = {
    val collector = new LocalClassCollector
    collector.traverse(fd)
    (collector.result, collector.localClasses)
  }

  private def laws(cd: LocalClassDef): Set[Identifier] = {
    cd.globalAncestors.map(_.cd).reverse.foldLeft(Map[Symbol, Identifier]()) {
      case (laws, cd) =>
        val methods = cd.methods
        val newLaws = methods
          .filter(id => symbols.getFunction(id).flags.exists(_.name == "law"))
          .map(id => id.symbol -> id)
        laws -- methods.map(_.symbol) ++ newLaws
    }.values.toSet
  }

  override protected def computeDependencyGraph: DiGraph[Identifier, SimpleEdge[Identifier]] = {
    var g = super.computeDependencyGraph

    symbols.functions.values foreach { fd =>
      val (deps, lcds) = collectClasses(fd)
      deps foreach { dep => g += SimpleEdge(fd.id, dep) }
      lcds foreach { lcd =>
        laws(lcd) foreach { law => g += SimpleEdge(law, fd.id) }
        g += SimpleEdge(fd.id, lcd.id)
      }
    }

    g
  }

}
