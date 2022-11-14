/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

import inox.evaluators.EvaluationResults.{EvaluatorError, RuntimeError, Successful}
import io.circe.*
import stainless.extraction.ExtractionSummary

import scala.concurrent.Future
import scala.util.{Failure, Success}

object DebugSectionEvaluator extends inox.DebugSection("eval")

/**
 * Evaluator Component
 *
 * Provides facilities to evaluate parameterless functions. It provides the
 * user with two results: the function's body value and whether or not, using
 * this value, the postcondition (if any) holds.
 *
 * Timeout is handled using --max-calls=<N>.
 */
object EvaluatorComponent extends Component { self =>
  override val name = "eval"
  override val description = "Evaluation of parameterless functions"

  override type Report = EvaluatorReport
  override type Analysis = EvaluatorAnalysis

  override val lowering = {
    class LoweringImpl(override val s: extraction.trees.type, override val t: extraction.trees.type)
      extends transformers.ConcreteTreeTransformer(s, t)
    inox.transformers.SymbolTransformer(new LoweringImpl(extraction.trees, extraction.trees))
  }

  override def run(pipeline: extraction.StainlessPipeline)(using inox.Context) = {
    new EvaluatorRun(pipeline)
  }
}

object EvaluatorRun {
  import stainless.trees._

  sealed abstract class FunctionStatus
  case class BodyFailed(error: String) extends FunctionStatus
  case class PostFailed(bodyValue: Expr, error: String) extends FunctionStatus
  case class NoPost(bodyValue: Expr) extends FunctionStatus
  case class PostHeld(bodyValue: Expr) extends FunctionStatus
  case class PostInvalid(bodyValue: Expr) extends FunctionStatus

  case class Result(fd: FunDef, status: FunctionStatus, time: Long)
}

class EvaluatorRun private(override val component: EvaluatorComponent.type,
                           override val trees: stainless.trees.type,
                           override val pipeline: extraction.StainlessPipeline)
                          (using override val context: inox.Context)
  extends ComponentRun {

  def this(pipeline: extraction.StainlessPipeline)(using inox.Context) =
    this(EvaluatorComponent, stainless.trees, pipeline)

  import trees._
  import component.{Report, Analysis}
  import EvaluatorRun._

  override def parse(json: Json): Report = EvaluatorReport.parse(json)

  private given givenDebugSection: DebugSectionEvaluator.type = DebugSectionEvaluator

  override def createFilter = EvaluatorCheckFilter(trees, context)

  override private[stainless] def execute(functions: Seq[Identifier], symbols: Symbols, exSummary: ExtractionSummary): Future[Analysis] = {
    import context.{given, _}

    val p = inox.Program(trees)(symbols)
    import p.{symbols => _, _}

    // Extract the body (with its precondition, if any) and the post condition (if any).
    def decomposeFunction(fd: FunDef): (Expr, Option[Expr]) = {
      import exprOps._
      val specced = BodyWithSpecs(fd.fullBody)
      val pre = specced.specs.filter(spec => spec.kind == LetKind || spec.kind == PreconditionKind)
      val nakedBodyOpt = specced.bodyOpt
      if (nakedBodyOpt.isEmpty) reporter.internalError(s"Unexpected empty body for ${fd.id}")
      val nakedBody = nakedBodyOpt.get
      val body = pre.foldRight(nakedBody) {
        case (spec @ LetInSpec(vd, e0), acc) => Let(vd, e0, acc).setPos(spec)
        case (spec @ Precondition(cond), acc) => Require(cond, acc).setPos(spec)
      }
      val postOpt = specced.getSpec(PostconditionKind)

      (body, postOpt.map(_.expr))
    }

    // Build an evaluator once and only if there is something to evaluate
    lazy val evaluator = p.getSemantics.getEvaluator

    // Evaluate an expression, logging events
    def evaluate(title: String, e: Expr): Either[String, Expr] = evaluator eval e match {
      case Successful(res) =>
        reporter.debug(s"\tGot $res from evaluation of $title.")
        Right(res)

      case RuntimeError(error) =>
        reporter.debug(s"\tRuntime error ($error) while evaluating $title.")
        Left(error)

      case EvaluatorError(error) =>
        reporter.internalError(s"Evaluator error ($error) while evaluating $title.")
    }

    // Evaluate the function's body and postcondition to determine its status
    def evalFunction(fd: FunDef): FunctionStatus = {
      val fid = fd.id
      reporter.info(s"Evaluating ${fid}")

      val (body, postOpt) = decomposeFunction(fd)
      val bodyValue = evaluate(s"$fid's body", body)

      val status = bodyValue match {
        case Left(error) => BodyFailed(error)
        case Right(value) if postOpt.isEmpty => NoPost(value)
        case Right(value) =>
          // Invoke the postcondition lambda
          val app = symbols.application(postOpt.get, Seq(value))
          val postValue = evaluate(s"$fid's PC", app)

          postValue match {
            case Left(error) => PostFailed(value, error)
            case Right(BooleanLiteral(true)) => PostHeld(value)
            case Right(BooleanLiteral(false)) => PostInvalid(value)
            case Right(res) => reporter.internalError(s"Unexpected result $res from postcondition evaluation.")
          }
      }

      reporter.info(s"Result for ${fid.asString} @${fd.getPos}:")

      status match {
        case BodyFailed(error) => reporter.warning(" => CRASHED")
        case PostFailed(body, error) => reporter.warning(" => POSTCONDITION CRASHED")
        case PostInvalid(body) => reporter.warning(" => POSTCONDITION INVALID")
        case PostHeld(body) => reporter.info(" => SUCCESSFUL (w/ postcondition)")
        case NoPost(body) => reporter.info(" => SUCCESSFUL")
      }

      val optError = status match {
        case BodyFailed(error) => Some(error)
        case PostFailed(_, error) => Some(error)
        case _ => None
      }

      optError.foreach(error => reporter.warning(s"  $error"))

      val optBody = status match {
        case PostFailed(body, _) => Some(body)
        case PostInvalid(body) => Some(body)
        case PostHeld(body) => Some(body)
        case NoPost(body) => Some(body)
        case _ => None
      }

      optBody.foreach(body => reporter.info(s"Body evaluates to:\n  ${body.asString.split("\n").mkString("\n  ")}"))

      status
    }

    // Measure how long it takes to determine the function' status
    def processFunction(fd: FunDef): Result = {
      val (time, tryStatus) = timers.evaluators.eval.runAndGetTime { evalFunction(fd) }
      tryStatus match {
        case Failure(e) => reporter.internalError(e)
        case Success(status) => Result(fd, status, time)
      }
    }

    reporter.debug(s"Processing ${functions.size} parameterless functions: ${functions mkString ", "}")

    Future.successful(new EvaluatorAnalysis {
      override val program = p
      override val sources = functions.toSet
      override val results = functions map (id => processFunction(symbols.getFunction(id)))
      override val extractionSummary = exSummary
    })
  }
}

