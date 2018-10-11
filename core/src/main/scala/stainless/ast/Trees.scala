/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

trait Trees
  extends inox.ast.Trees
     with Definitions
     with Expressions
     with Constructors
     with Deconstructors
     with TreeOps { self =>

  type Symbol = ast.Symbol
  type SymbolIdentifier = ast.SymbolIdentifier

  object patternOps extends {
    protected val sourceTrees: Trees.this.type = Trees.this
    protected val targetTrees: Trees.this.type = Trees.this
  } with inox.ast.GenTreeOps {
    type Source = Pattern
    type Target = Pattern

    override def transform[E](pattern: Pattern, env: E)(
      op: (Pattern, E, inox.transformers.TransformerOp[Pattern, E, Pattern]) => Pattern
    ): Pattern = new transformers.TransformerWithPatternOp {
      override val s: self.type = self
      override val t: self.type = self
      override val patternOp = op
      override type Env = E
    }.transform(pattern, env)

    override def traverse[E](pattern: Pattern, env: E)(
      op: (Pattern, E, inox.transformers.TraverserOp[Pattern, E]) => Unit
    ): Unit = new transformers.TraverserWithPatternOp {
      override val trees: self.type = self
      override val patternOp = op
      override type Env = E
    }.traverse(pattern, env)
  }

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps

  val printer: Printer { val trees: self.type }
}
