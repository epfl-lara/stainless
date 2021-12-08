/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

trait TreeOps extends inox.ast.TreeOps { self: Trees =>

  trait StainlessSelfTransformer extends transformers.Transformer with SelfTransformer

  trait StainlessSelfTreeTransformer extends transformers.TreeTransformer with SelfTreeTransformer

  trait StainlessSelfTraverser extends transformers.Traverser with SelfTraverser

  trait StainlessSelfTreeTraverser extends transformers.TreeTraverser with SelfTreeTraverser

  // Implementation of these traits as classes, as a conveniance when we want to create an anonymous transformer/traverser.

  class ConcreteStainlessSelfTransformer(override val s: self.type, override val t: self.type) extends StainlessSelfTransformer {
    def this() = this(self, self)
  }

  class ConcreteStainlessSelfTreeTransformer(override val s: self.type, override val t: self.type) extends StainlessSelfTreeTransformer {
    def this() = this(self, self)
  }

  class ConcreteStainlessSelfTraverser(override val trees: self.type) extends StainlessSelfTraverser {
    def this() = this(self)
  }

  class ConcreteStainlessSelfTreeTraverser(override val trees: self.type) extends StainlessSelfTreeTraverser {
    def this() = this(self)
  }

}

