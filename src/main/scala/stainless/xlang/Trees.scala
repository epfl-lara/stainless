/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

trait Trees
  extends ast.Trees
     with Expressions
     with Extractors
     with Types {

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps
}

