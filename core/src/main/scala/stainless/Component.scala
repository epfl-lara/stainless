/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}

trait Component {
  val name: String
  val description: String

  type Report <: AbstractReport

  val lowering: inox.ast.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }

  trait AbstractReport {
    def emit(): Unit
    def emitJson(): Unit
  }

  def apply(units: List[xt.UnitDef], program: Program { val trees: xt.type }): Report
}

object optFunctions extends inox.OptionDef[Seq[String]] {
  val name = "functions"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

trait SimpleComponent extends Component { self =>
  val trees: ast.Trees
  import trees._

  def extract(program: Program { val trees: xt.type }): Program { val trees: self.trees.type } = {
    val checker = inox.ast.SymbolTransformer(new extraction.CheckingTransformer {
      val s: extraction.trees.type = extraction.trees
      val t: self.trees.type = self.trees
    })

    val lowering = MainHelpers.components.filterNot(_ == this).foldRight(checker) {
      (l, r) => l.lowering andThen r
    }

    program.transform(extraction.extractor andThen lowering)
  }

  def apply(units: List[xt.UnitDef], program: Program { val trees: xt.type }): Report = {
    val extracted = extract(program)
    import extracted._

    val relevant = symbols.functions.values.filterNot { fd =>
      (fd.flags contains "library") || (fd.flags contains "unchecked")
    }.map(_.id).toSeq

    val functions = ctx.options.findOption(optFunctions) match {
      case Some(names) => relevant.filter(id => names contains id.name)
      case None => relevant
    }

    apply(functions, extracted)
  }

  def apply(functions: Seq[Identifier], program: Program { val trees: self.trees.type }): Report
}
