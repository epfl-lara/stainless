/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import utils.{CheckFilter, DefinitionIdFinder, DependenciesFinder}
import extraction.xlang.{trees => xt}
import io.circe._

import scala.concurrent.Future

trait Component { self =>
  val name: String
  val description: String

  type Report <: AbstractReport[Report]
  type Analysis <: AbstractAnalysis { type Report = self.Report }

  val lowering: inox.transformers.SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  }

  def run(pipeline: extraction.StainlessPipeline)(using inox.Context): ComponentRun { val component: self.type }
}

object optFunctions extends inox.OptionDef[Seq[String]] {
  val name = "functions"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

object optCompareFuns extends inox.OptionDef[Seq[String]] {
  val name = "comparefuns"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

object optModels extends inox.OptionDef[Seq[String]] {
  val name = "models"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

trait ComponentRun { self =>
  val component: Component
  val trees: ast.Trees
  val context: inox.Context
  protected val pipeline: extraction.StainlessPipeline

  import context.{given, _}
  import component.{Report, Analysis}

  def parse(json: Json): Report

  protected final val lowering: extraction.ExtractionPipeline {
    val s: extraction.trees.type
    val t: extraction.trees.type
  } = {
    val otherComponents = MainHelpers.components.filterNot(_ == component)
    if (otherComponents.isEmpty) {
      class TransformerImpl(override val s: extraction.trees.type, override val t: extraction.trees.type)
        extends transformers.ConcreteTreeTransformer(s, t)
      val transformer = new TransformerImpl(extraction.trees, extraction.trees)
      extraction.ExtractionPipeline(transformer)
    } else {
      val transformer = otherComponents.map(_.lowering).reduceLeft(_ andThen _)
      extraction.ExtractionPipeline(transformer)
    }
  }

  /* Override point for pipeline extensions in certain components.
   * For example, the partial evaluator and measure inference pipeline in the verification component. */
  protected def createPipeline: extraction.StainlessPipeline = pipeline andThen lowering

  private[this] final val extractionPipeline = createPipeline andThen extraction.completer(trees)

  /* Override point for filter extensions in certain components.
   * For example, the evaluating component only evaluates parameterless functions. */
  protected def createFilter: CheckFilter { val trees: self.trees.type } = CheckFilter(trees, context)

  private[this] final val extractionFilter = createFilter

  /** Sends the symbols through the extraction pipeline. */
  def extract(symbols: xt.Symbols): trees.Symbols = extractionPipeline extract symbols

  /** Sends the program's symbols through the extraction pipeline. */
  def extract(program: inox.Program { val trees: xt.type }): inox.Program {
    val trees: self.trees.type
  } = inox.Program(trees)(extract(program.symbols))

  /** Passes the provided symbols through the extraction pipeline and compute all
    * functions to process that are derived from the provided identifiers. */
  def apply(ids: Seq[Identifier], symbols: xt.Symbols): Future[Analysis] = {
    val exSymbols = extract(symbols)
    val toProcess = extractionFilter.filter(ids, exSymbols, component)
    execute(toProcess, exSymbols)
  }

  def apply(id: Identifier, symbols: xt.Symbols): Future[Analysis] =
    apply(Seq(id), symbols)

  private[stainless] def execute(functions: Seq[Identifier], symbols: trees.Symbols): Future[Analysis]
}

