/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}

trait Component {
  val name: String

  val lowering: inox.ast.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }

  def apply(packages: List[xt.PackageDef], program: Program { val trees: xt.type }): Unit
}

trait SimpleComponent { self =>
  val trees: ast.Trees

  def apply(packages: List[xt.PackageDef], program: Program { val trees: xt.type }): Unit = {
    val checker = inox.ast.SymbolTransformer(new extraction.CheckingTransformer {
      val s: extraction.trees.type = extraction.trees
      val t: self.trees.type = self.trees
    })

    val lowering = Main.components.values.filterNot(_ == this).foldRight(checker) {
      (l, r) => l.lowering andThen r
    }

    val extracted = program.transform(extraction.extractor andThen lowering)

    apply(extracted)
  }

  def apply(program: Program { val trees: self.trees.type }): Unit
}
