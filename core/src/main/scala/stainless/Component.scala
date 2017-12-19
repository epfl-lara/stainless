/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}
import utils.CheckFilter

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

  type SelfProgram = Program { val trees: self.trees.type }

  def extract(program: Program { val trees: xt.type }, ctx: inox.Context): SelfProgram = {
    val checker = inox.ast.SymbolTransformer(new extraction.CheckingTransformer {
      val s: extraction.trees.type = extraction.trees
      val t: self.trees.type = self.trees
    })

    val lowering = MainHelpers.components.filterNot(_ == this).foldRight(checker) {
      (l, r) => l.lowering andThen r
    }

    try {
      extraction.extract(program, ctx).transform(lowering)
    } catch {
      case extraction.MissformedStainlessCode(tree, msg) =>
        ctx.reporter.fatalError(tree.getPos, msg)
    }
  }

  private val marks = new utils.AtomicMarks[Identifier]
  def onCycleBegin(): Unit = marks.clear()

  // Subclasses can customise the filter here.
  protected def createFilter(trees: self.trees.type, ctx: inox.Context): CheckFilter {
    val trees: self.trees.type
  } = CheckFilter(trees, ctx)

  // Subclasses should use this method to determine which functions should be processed or not.
  protected final def filter(program: SelfProgram, ctx: inox.Context)
                            (functions: Seq[Identifier]): Seq[program.trees.FunDef] = {
    import program.symbols
    import program.trees._
    import ctx.reporter

    val filter = createFilter(program.trees, ctx)

    val toProcess = functions
      . map { fid => symbols.getFunction(fid) }
      . filter { fd => filter.shouldBeChecked(fd) && marks.compareAndSet(fd.id) }

    for (fd <- toProcess) {
      if (fd.flags contains "library") {
        val fullName = fd.id.fullName
        reporter.warning(s"Component [$name]: Forcing processing of $fullName which was assumed verified")
      }
    }

    toProcess
  }


  def apply(program: Program { val trees: xt.type }, ctx: inox.Context): Analysis = {
    val extracted = extract(program, ctx)
    val functions = extracted.symbols.functions.values.toSeq map { _.id }
    apply(functions, extracted, ctx)
  }

  def apply(functions: Seq[Identifier], program: SelfProgram, ctx: inox.Context): Analysis
}

