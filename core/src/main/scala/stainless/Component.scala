/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}
import utils.CheckFilter

import io.circe._

import scala.concurrent.Future

import scala.language.existentials

trait Component { self =>
  val name: String
  val description: String

  type Report <: AbstractReport[Report]
  type Analysis <: AbstractAnalysis { type Report = self.Report }

  val lowering: inox.ast.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }

  def run(pipeline: extraction.StainlessPipeline)(implicit context: inox.Context): ComponentRun { val component: self.type }
}

object optFunctions extends inox.OptionDef[Seq[String]] {
  val name = "functions"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

object optDebugObjects extends inox.OptionDef[Seq[String]] {
  val name = "debug-objects"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "o1,o2,..."
}

object optDebugPhases extends inox.OptionDef[Seq[String]] {
  val name = "debug-phases"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "p1,p2,..."
}

trait ComponentRun { self =>
  val component: Component
  val trees: ast.Trees
  implicit val context: inox.Context
  protected val pipeline: extraction.StainlessPipeline

  import context._
  import component.{Report, Analysis}

  def parse(json: Json): Report

  protected final val lowering: extraction.ExtractionPipeline {
    val s: extraction.trees.type
    val t: extraction.trees.type
  } = {
    val otherComponents = MainHelpers.components.filterNot(_ == component)
    if (otherComponents.isEmpty) {
      extraction.ExtractionPipeline(new ast.TreeTransformer {
        override val s: extraction.trees.type = extraction.trees
        override val t: extraction.trees.type = extraction.trees
      })
    } else {
      extraction.ExtractionPipeline(otherComponents.map(_.lowering).reduceLeft(_ andThen _))
    }
  }

  /* Override point for pipeline extensions in certain components.
   * For example, the partial evaluator pipeline in the verification component. */
  protected def createPipeline: extraction.StainlessPipeline = pipeline andThen lowering

  private[this] final val extractionPipeline = createPipeline andThen extraction.completer(trees)

  /* Override point for filter extensions in certain components.
   * For example, the evaluating component only evaluates parameterless functions. */
  protected def createFilter: CheckFilter { val trees: self.trees.type } = CheckFilter(trees, context)

  private[this] final val extractionFilter = createFilter

  /** Sends the symbols through the extraction pipeline. */
  def extract(symbols: extraction.xlang.trees.Symbols): trees.Symbols = extractionPipeline extract symbols

  /** Sends the program's symbols through the extraction pipeline. */
  def extract(program: inox.Program { val trees: extraction.xlang.trees.type }): inox.Program {
    val trees: self.trees.type
  } = inox.Program(trees)(extract(program.symbols))

  /** Passes the provided symbols through the extraction pipeline and processes all
    * functions derived from the provided identifier. */
  def apply(id: Identifier, symbols: extraction.xlang.trees.Symbols): Future[Analysis] = try {

    val exSymbols = extract(symbols)

    val toCheck = inox.utils.fixpoint { (ids: Set[Identifier]) =>
      ids ++ exSymbols.functions.values.toSeq
        .filter(_.flags.exists { case trees.Derived(id) => ids(id) case _ => false })
        .filter(extractionFilter.shouldBeChecked)
        .map(_.id)
    } (exSymbols.lookupFunction(id).filter(extractionFilter.shouldBeChecked).map(_.id).toSet)

    val toProcess = toCheck.toSeq.sortBy(exSymbols.getFunction(_).getPos)

    for (id <- toProcess) {
      val fd = exSymbols.getFunction(id)
      if (fd.flags exists (_.name == "library")) {
        val fullName = fd.id.fullName
        reporter.warning(s"Component [${component.name}]: Forcing processing of $fullName which was assumed verified")
      }
    }

    apply(toProcess, exSymbols)
  } catch {
    case extraction.MissformedStainlessCode(tree, msg) =>
      reporter.fatalError(tree.getPos, msg)
  }

  private[stainless] def apply(functions: Seq[Identifier], symbols: trees.Symbols): Future[Analysis]
}

