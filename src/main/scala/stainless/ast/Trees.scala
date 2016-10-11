/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait Trees
  extends inox.ast.Trees
     with Expressions
     with Extractors
     with Printers
     with TreeOps {

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

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols
    with TypeOps
    with SymbolOps { self0: Symbols =>
  }
}
