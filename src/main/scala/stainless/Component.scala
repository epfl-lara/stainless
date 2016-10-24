/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}

trait Component {
  val name: String
  val description: String

  val lowering: inox.ast.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }

  def apply(units: List[xt.UnitDef], program: Program { val trees: xt.type }): Unit
}

object optFunctions extends inox.OptionDef[Seq[String]] {
  val name = "functions"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

trait SimpleComponent extends Component { self =>
  val trees: ast.Trees

  def apply(units: List[xt.UnitDef], program: Program { val trees: xt.type }): Unit = {
    val checker = inox.ast.SymbolTransformer(new extraction.CheckingTransformer {
      val s: extraction.trees.type = extraction.trees
      val t: self.trees.type = self.trees
    })

    val lowering = Main.components.filterNot(_ == this).foldRight(checker) {
      (l, r) => l.lowering andThen r
    }

    val extracted = program.transform(extraction.extractor andThen lowering)

    val mainFunctions = units.filter(_.isMain).flatMap(_.allFunctions(program.symbols))
    val functions = program.ctx.options.findOption(optFunctions) match {
      case Some(names) => mainFunctions.filter(id => names contains id.name)
      case None => mainFunctions
    }

    apply(functions, extracted)
  }

  def apply(functions: Seq[Identifier], program: Program { val trees: self.trees.type }): Unit
}
