/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import inox.utils.Graphs._

trait CallGraph extends inox.ast.CallGraph { self =>
  protected val trees: Trees
  import trees._

  protected trait StainlessFunctionCollector extends StainlessSelfTreeTraverser with FunctionCollector {
    // The witness of a function (`PrecondWitness`) calls the function, but is never evaluated: this
    // call doesn't make the function recursive. Its other calls are dependencies of the function.
    private var currentFunction: Option[Identifier] = None
    private var inWitness: Boolean = false

    override protected def register(id: Identifier): Unit =
      if (!(inWitness && currentFunction.contains(id))) super.register(id)

    override def traverse(fd: FunDef): Unit = {
      currentFunction = Some(fd.id)
      super.traverse(fd)
    }

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
      case PrecondWitness(_) =>
        inWitness = true
        try super.traverse(flag) finally inWitness = false
      case _ =>
        super.traverse(flag)
    }
  }
  // Used as a default implementation for the trait StainlessFunctionCollector
  protected class ConcreteStainlessFunctionCollector extends ConcreteStainlessSelfTreeTraverser with StainlessFunctionCollector

  override protected def getFunctionCollector = new ConcreteStainlessFunctionCollector
}

trait DependencyGraph extends inox.ast.DependencyGraph with CallGraph {
  import trees._

  protected trait StainlessSortCollector extends StainlessSelfTreeTraverser with SortCollector {
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
  // Used as a default implementation for the trait StainlessSortCollector
  protected class ConcreteStainlessSortCollector extends ConcreteStainlessSelfTreeTraverser with StainlessSortCollector

  override def getSortCollector = new ConcreteStainlessSortCollector
}
