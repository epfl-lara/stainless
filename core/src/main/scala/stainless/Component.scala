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

  // Subclasses can customise the filter here.
  protected def filterFromContext(ctx: inox.Context): utils.CheckFilter = utils.CheckFilter(ctx)

  // Subclasses should use this method to determine which functions should be processed or not.
  protected final def filter(program: Program { val trees: self.trees.type }, ctx: inox.Context)
                            (functions: Seq[Identifier]): Seq[Identifier] = {
    val filter = filterFromContext(ctx)
    import program.symbols

    functions
      . map { fid => symbols.getFunction(fid) }
      . filter { fd => filter.shouldBeChecked(fd.id, fd.flags) && marks.compareAndSet(fd.id) }
      . map { fd => fd.id }
  }


  def apply(program: Program { val trees: xt.type }, ctx: inox.Context): Analysis = {
    val extracted = extract(program, ctx)
    val functions = extracted.symbols.functions.values.toSeq map { _.id }
    apply(functions, extracted, ctx)
  }

  def apply(functions: Seq[Identifier], program: Program { val trees: self.trees.type }, ctx: inox.Context): Analysis
}

