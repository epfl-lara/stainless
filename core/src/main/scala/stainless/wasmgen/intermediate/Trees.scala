/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

trait Trees
  extends stainless.ast.Trees
    with Definitions
    with Expressions
    with Types
    with Constructors
    with Deconstructors
    with TreeOps { self =>

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps

  val printer: Printer { val trees: self.type }
}
