/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import inox.utils.{ Position, NoPosition }
import utils.{CheckFilter, DefinitionIdFinder, DependenciesFinder}

import extraction.xlang.{trees => xt}
import extraction.throwing.{trees => tt}
import extraction._

import stainless.utils.JsonConvertions.given

import io.circe._
import io.circe.syntax._
import io.circe.generic.semiauto._

import scala.concurrent.Future

import ExtraOps._
import GenCReport._

object GenCComponent extends Component { self =>
  override val name = "genc"
  override val description = "Convert code to C (implies --batched)"

  override type Report = GenCReport
  override type Analysis = GenCAnalysis

  override val lowering = {
    class LoweringImpl(override val s: extraction.trees.type, override val t: extraction.trees.type)
      extends transformers.ConcreteTreeTransformer(s, t)
    inox.transformers.SymbolTransformer(new LoweringImpl(extraction.trees, extraction.trees))
  }

  override def run(pipeline: extraction.StainlessPipeline)(using inox.Context) = {
    new GenCRun(pipeline)
  }
}

object GenCRun {
  case class Result(fd: xt.FunDef, status: GenCReport.Status, time: Long)

  def pipelineBegin(using inox.Context): ExtractionPipeline{val s: xt.type; val t: tt.type} =
    xlang.extractor        `andThen`
      innerclasses.extractor `andThen`
      utils.NamedPipeline("Laws",            methods.Laws(methods.trees))            `andThen`
      utils.NamedPipeline("SuperInvariants", methods.SuperInvariants(methods.trees)) `andThen`
      utils.NamedPipeline("SuperCalls",      methods.SuperCalls(methods.trees))      `andThen`
      // No Sealing with GenC
      // utils.DebugPipeline("Sealing",         methods.Sealing(methods.trees))         andThen
      utils.NamedPipeline("MethodLifting",   methods.MethodLifting(methods.trees))   `andThen`
      utils.NamedPipeline("MergeInvariants", methods.MergeInvariants(methods.trees)) `andThen`
      utils.NamedPipeline("FieldAccessors",  methods.FieldAccessors(methods.trees))  `andThen`
      utils.NamedPipeline("ValueClasses",    methods.ValueClasses(methods.trees))    `andThen`
      methods.lowering `andThen`
      utils.NamedPipeline("LeonInlining", LeonInlining(tt, tt))
}

class GenCRun private(override val component: GenCComponent.type,
                      override val trees: xt.type,
                      override val pipeline: extraction.StainlessPipeline)
                     (using override val context: inox.Context)
  extends ComponentRun {

  def this(pipeline: extraction.StainlessPipeline)(using inox.Context) =
    this(GenCComponent, xt, pipeline)

  import xt._

  override def apply(ids: Seq[Identifier], symbols: Symbols): Future[GenCComponent.Analysis] = try {
    val (symbolsAfterPipeline: tt.Symbols, exSummary) = GenCRun.pipelineBegin.extract(symbols)

    GenerateC.emit(symbolsAfterPipeline)

    val p = inox.Program(trees)(symbols)

    Future.successful(new GenCAnalysis {
      override val program = p
      override val sources = ids.toSet
      override val results = ids.flatMap { id =>
        val fd = symbols.getFunction(id)
        val pos = fd.getPos.toString
        if (fd.flags.exists(_.name == "cCode.export") && !fd.isAccessor)
          Some(GenCRun.Result(fd, Compiled, 0))
        else
          None
      }
      override val extractionSummary = exSummary
    })
  } catch {
    case extraction.MalformedStainlessCode(tree, msg) =>
      context.reporter.fatalError(tree.getPos, msg)
  }

  override private[stainless] def execute(functions: Seq[Identifier], symbols: Symbols, exSummary: ExtractionSummary): Future[GenCComponent.Analysis] = ???

  def parse(json: io.circe.Json): GenCReport = ???

}

object GenCReport {
  sealed abstract class Status
  case object Compiled extends Status
  case object CompilationError extends Status

  given statusDecoder: Decoder[Status] = deriveDecoder
  given statusEncoder: Encoder[Status] = deriveEncoder

  case class Record(id: Identifier, pos: Position, status: Status, time: Long) extends AbstractReportHelper.Record {
    override val derivedFrom = id
  }

  private def levelOf(status: Status) = status match {
    case Compiled => Level.Normal
    case CompilationError => Level.Error
  }

  private def descriptionOf(status: Status): String = status match {
    case Compiled => "exported C"
    case CompilationError => "error during C compilation"
  }

  given recordDecoder: Decoder[Record] = deriveDecoder
  given recordEncoder: Encoder[Record] = deriveEncoder
}

case class GenCReport(results: Seq[Record], sources: Set[Identifier], override val extractionSummary: ExtractionSummary) extends BuildableAbstractReport[Record, GenCReport] {

  override val name = GenCComponent.name

  override def annotatedRows: Seq[RecordRow] = results.map {
    case Record(id, pos, status, time) => RecordRow(id, pos, levelOf(status), Seq(descriptionOf(status)), time, None)
  }

  protected def build(results: Seq[Record], sources: Set[Identifier]): GenCReport =
    GenCReport(results, sources, ExtractionSummary.NoSummary)

  override protected val encoder: io.circe.Encoder[Record] = GenCReport.recordEncoder

  private lazy val totalTime = (results map { _.time }).sum
  private lazy val totalValid = results.size
  private lazy val totalInvalid = results.size - totalValid

  override lazy val stats =
    ReportStats(results.size, totalTime, totalValid, validFromCache = 0, trivial = 0, totalInvalid, unknown = 0)
}
