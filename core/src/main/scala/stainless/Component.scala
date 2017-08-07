/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}
import scala.language.existentials

object optFunctions extends inox.OptionDef[Seq[String]] {
  val name = "functions"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

trait Component {
  val name: String
  val description: String

  type Report <: AbstractReport

  val lowering: inox.ast.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }
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

    extraction.extract(program).transform(lowering)
  }

  def apply(program: Program { val trees: xt.type }): Report = {
    val extracted = extract(program)
    import extracted._

    val filter = new utils.CheckFilter { override val ctx = extracted.ctx }
    val relevant = symbols.functions.values.toSeq filter { fd =>
      filter.shouldBeChecked(fd.id, fd.flags)
    } map { _.id }

    apply(relevant, extracted)
  }

  def apply(functions: Seq[Identifier], program: Program { val trees: self.trees.type }): Report
}

