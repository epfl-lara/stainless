/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import inox.utils.{ Position, NoPosition }
import utils.{CheckFilter, DefinitionIdFinder, DependenciesFinder}

import extraction.xlang.{trees => xt}
import extraction.throwing.{trees => tt}
import extraction._

import stainless.utils.JsonConvertions._

import io.circe._
import io.circe.syntax._
import io.circe.generic.semiauto._

import scala.concurrent.Future

import scala.language.existentials

import ExtraOps._
import GenCReport._

object GenCComponent extends Component { self =>
  override val name = "genc"
  override val description = "Convert code to C (implies --batched)"

  override type Report = GenCReport
  override type Analysis = GenCAnalysis

  override val lowering = inox.transformers.SymbolTransformer(new transformers.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  override def run(pipeline: extraction.StainlessPipeline)(implicit ctx: inox.Context) = {
    new GenCRun(pipeline)
  }
}

object GenCRun {
  case class Result(fd: xt.FunDef, status: GenCReport.Status, time: Long)
}

class GenCRun(override val pipeline: extraction.StainlessPipeline) // pipeline is ignored here, should be refactored
             (override implicit val context: inox.Context) extends {
  override val component = GenCComponent
  override val trees: xt.type = xt
} with ComponentRun {

  import xt._

  // We only keep some parts of the standard verification pipeline for genc
  val pipelineBegin: ExtractionPipeline{val s: xt.type; val t: tt.type} =
    xlang.extractor        andThen
    innerclasses.extractor andThen
    utils.DebugPipeline("Laws",            methods.Laws(methods.trees))            andThen
    utils.DebugPipeline("SuperInvariants", methods.SuperInvariants(methods.trees)) andThen
    utils.DebugPipeline("SuperCalls",      methods.SuperCalls(methods.trees))      andThen
    // No Sealing with GenC
    // utils.DebugPipeline("Sealing",         methods.Sealing(methods.trees))         andThen
    utils.DebugPipeline("MethodLifting",   methods.MethodLifting(methods.trees))   andThen
    utils.DebugPipeline("MergeInvariants", methods.MergeInvariants(methods.trees)) andThen
    utils.DebugPipeline("FieldAccessors",  methods.FieldAccessors(methods.trees))  andThen
    utils.DebugPipeline("ValueClasses",    methods.ValueClasses(methods.trees))    andThen
    methods.lowering andThen
    utils.DebugPipeline("LeonInlining", LeonInlining(tt, tt))

  override def apply(ids: Seq[Identifier], symbols: Symbols): Future[GenCComponent.Analysis] = try {
    val symbolsAfterPipeline: tt.Symbols = pipelineBegin.extract(symbols)

    GenerateC.run(symbolsAfterPipeline)

    val p = inox.Program(trees)(symbols)

    Future.successful(new GenCAnalysis {
      override val program = p
      override val sources = ids.toSet
      override val results = ids.flatMap { id =>
        val fd = symbols.getFunction(id)
        val pos = fd.getPos.toString
        if (fd.flags.exists(_.name == "cCode.export"))
          Some(GenCRun.Result(fd, Compiled, 0))
        else
          None
      }
    })
  } catch {
    case extraction.MalformedStainlessCode(tree, msg) =>
      context.reporter.fatalError(tree.getPos, msg)
  }

  private[stainless] def execute(functions: Seq[Identifier], symbols: Symbols): Future[GenCComponent.Analysis] = ???

  def parse(json: io.circe.Json): GenCReport = ???

}

object GenCReport {
  sealed abstract class Status
  case object Compiled extends Status
  case object CompilationError extends Status

  implicit val statusDecoder: Decoder[Status] = deriveDecoder
  implicit val statusEncoder: Encoder[Status] = deriveEncoder

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

  implicit val recordDecoder: Decoder[Record] = deriveDecoder
  implicit val recordEncoder: Encoder[Record] = deriveEncoder
}

case class GenCReport(results: Seq[Record], sources: Set[Identifier]) extends BuildableAbstractReport[Record, GenCReport] {

  override val name = GenCComponent.name

  override def annotatedRows: Seq[RecordRow] = results.map {
    case Record(id, pos, status, time) => RecordRow(id, pos, levelOf(status), Seq(descriptionOf(status)), time)
  }

  protected def build(results: Seq[Record], sources: Set[Identifier]): GenCReport =
    new GenCReport(results, sources)

  implicit protected val encoder: io.circe.Encoder[Record] = recordEncoder

  private lazy val totalTime = (results map { _.time }).sum
  private lazy val totalValid = results.size
  private lazy val totalInvalid = results.size - totalValid

  override lazy val stats =
    ReportStats(results.size, totalTime, totalValid, validFromCache = 0, totalInvalid, unknown = 0)
}
