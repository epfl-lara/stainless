/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}
import utils.CheckFilter

import scala.concurrent.Future

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

  def apply(program: Program { val trees: xt.type }, ctx: inox.Context): Future[Analysis] = {
    val extracted = extract(program, ctx)
    import extracted.trees._

    val filter = createFilter(extracted.trees, ctx)
    val toProcess = extracted.symbols.functions.values.toSeq
      .filter(fd => filter.shouldBeChecked(fd) && marks.compareAndSet(fd.id))

    for (fd <- toProcess) {
      if (fd.flags contains "library") {
        val fullName = fd.id.fullName
        ctx.reporter.warning(s"Component [$name]: Forcing processing of $fullName which was assumed verified")
      }
    }

    apply(toProcess.map(_.id), extracted, ctx)
  }

  def apply(functions: Seq[Identifier], program: SelfProgram, ctx: inox.Context): Future[Analysis]
}

