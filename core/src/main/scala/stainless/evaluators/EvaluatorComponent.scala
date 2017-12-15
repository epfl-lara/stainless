/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package evaluators

import inox.evaluators.EvaluationResults.{ EvaluatorError, RuntimeError, Successful }

import scala.language.existentials
import scala.util.{ Success, Failure }

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
object EvaluatorComponent extends SimpleComponent { self =>
  override val name = "eval"
  override val description = "Evaluation of parameterless functions"

  override val trees: stainless.trees.type = stainless.trees
  import trees.{ exprOps, BooleanLiteral, Expr, FunDef }

  override type Analysis = EvaluatorAnalysis
  implicit val debugSection = DebugSectionEvaluator

  override val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  override def createFilter(trees: self.trees.type, ctx: inox.Context) =
    EvaluatorCheckFilter(trees, ctx)

  sealed abstract class FunctionStatus
  case class BodyFailed(error: String) extends FunctionStatus
  case class PostFailed(bodyValue: Expr, error: String) extends FunctionStatus
  case class NoPost(bodyValue: Expr) extends FunctionStatus
  case class PostHeld(bodyValue: Expr) extends FunctionStatus
  case class PostInvalid(bodyValue: Expr) extends FunctionStatus

  case class Result(fd: FunDef, status: FunctionStatus, time: Long)

  override def apply(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context): Analysis = {
    import ctx.{ implicitContext, reporter, timers }
    import p.{ symbols }

    // Extract the body (with its precondition, if any) and the post condition (if any).
    def decomposeFunction(fd: FunDef): (Expr, Option[Expr]) = {
      val preOpt = exprOps preconditionOf fd.fullBody
      val nakedBodyOpt = exprOps withoutSpecs fd.fullBody
      if (nakedBodyOpt.isEmpty) reporter.internalError(s"Unexpected empty body for ${fd.id}")
      val nakedBody = nakedBodyOpt.get
      val postOpt = exprOps postconditionOf fd.fullBody

      val body = exprOps.withPrecondition(nakedBody, preOpt)

      (body, postOpt)
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
      reporter.debug(s"Evaluating ${fid}")

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

      reporter.debug(s"Result for ${fid}: $status")

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

    val toEval = filter(p, ctx)(funs).toList // Ensure we don't have a Stream beyond this point

    reporter.debug(s"Processing ${toEval.size} parameterless functions: ${toEval mkString ", "}")

    new EvaluatorAnalysis {
      val program = p
      val results = toEval map processFunction
    }
  }
}

