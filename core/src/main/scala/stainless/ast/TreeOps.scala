/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

trait TreeOps extends inox.ast.TreeOps { self: Trees =>

  trait SelfTransformer extends transformers.Transformer with super.SelfTransformer

  trait SelfTreeTransformer extends transformers.TreeTransformer with super.SelfTreeTransformer

  trait Traverser extends transformers.Traverser with super.Traverser

  trait TreeTraverser extends transformers.TreeTraverser with super.TreeTraverser
}

