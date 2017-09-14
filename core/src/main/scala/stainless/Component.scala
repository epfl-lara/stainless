/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}
import scala.language.existentials

trait Component {
  val name: String
  val description: String

  type Analysis <: AbstractAnalysis

  val lowering: inox.ast.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }
}

object optFunctions extends inox.OptionDef[Seq[String]] {
  val name = "functions"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

trait SimpleComponent extends Component { self =>
  val trees: ast.Trees

  def extract(program: Program { val trees: xt.type }, ctx: inox.Context): Program { val trees: self.trees.type } = {
    val checker = inox.ast.SymbolTransformer(new extraction.CheckingTransformer {
      val s: extraction.trees.type = extraction.trees
      val t: self.trees.type = self.trees
    })

    val lowering = MainHelpers.components.filterNot(_ == this).foldRight(checker) {
      (l, r) => l.lowering andThen r
    }

    extraction.extract(program, ctx).transform(lowering)
  }

  private val marks = new utils.AtomicMarks[Identifier]
  def onCycleBegin(): Unit = marks.clear()

  def apply(program: Program { val trees: xt.type }, ctx: inox.Context): Analysis = {
    val extracted = extract(program, ctx)
    import extracted._

    val filter = new utils.CheckFilter { override val context = ctx }
    val relevant = symbols.functions.values.toSeq filter { fd =>
      filter.shouldBeChecked(fd.id, fd.flags) && marks.compareAndSet(fd.id)
    } map { _.id }

    apply(relevant, extracted, ctx)
  }

  def apply(functions: Seq[Identifier], program: Program { val trees: self.trees.type }, ctx: inox.Context): Analysis
}

