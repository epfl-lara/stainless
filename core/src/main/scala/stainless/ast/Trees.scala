/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

trait Trees
  extends inox.ast.Trees
     with Definitions
     with Expressions
     with Types
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

    lazy val Deconstructor = PatternExtractor
  }

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps

  val printer: Printer { val trees: self.type }
}
