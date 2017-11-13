/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package forcing

import inox.solvers.PurityOptions
import inox.evaluators.EvaluationResults._

import stainless.extraction.Trees

object DebugSectionForcing extends inox.DebugSection("forcing")

class Forcing(
  override val sourceProgram: StainlessProgram,
  val context: inox.Context
) extends inox.ast.ProgramTransformer { self =>

  import context._
  import sourceProgram._
  import sourceProgram.trees._
  import sourceProgram.symbols._
  import sourceProgram.trees.exprOps._

  override final object encoder extends IdentityTreeTransformer
  override final object decoder extends IdentityTreeTransformer

  implicit val debugSection = DebugSectionForcing

  implicit private val semantics = sourceProgram.getSemantics

  override final lazy val targetProgram: Program { val trees: sourceProgram.trees.type } = {
    inox.Program(sourceProgram.trees)(transform(sourceProgram.symbols))
  }

  object transformer extends IdentityTreeTransformer

  private val evaluator = semantics.getEvaluator

  private def transform(syms: Symbols): Symbols = {
    def shouldForce(fi: FunctionInvocation): Boolean = {
      syms.functions(fi.id).flags.contains(Force) && isGround(fi)
    }

    NoSymbols
      .withADTs(symbols.adts.values.map(transformer.transform).toSeq)
      .withFunctions(symbols.functions.values.toSeq.map { fd =>
        val forcedBody = exprOps.postMap {
          case fi: FunctionInvocation if shouldForce(fi) => Some(force(fi))
          case _ => None
        } (fd.fullBody)

        transformer.transform(fd.copy(fullBody = forcedBody, flags = fd.flags - Force))
      })
  }

  private def force(fi: FunctionInvocation): Expr = {
    reporter.debug(s"Forcing invocation of `${fi.id}` @ ${fi.getPos}...")
    reporter.debug(s" - Before: $fi...")
    val res = evaluator.eval(fi) match {
      case Successful(e) => exprOps.freshenLocals(e)
      case error =>
        context.reporter.error(ForcingError(fi, error))
        fi
    }
    reporter.debug(s" - After: $res")
    res
  }

  case class ForcingError(expr: Expr, result: Result[Expr]) {
    val error: String = result match {
      case RuntimeError(msg) =>
        s"runtime error: $msg"
      case EvaluatorError(msg) =>
        s"evaluator error: $msg"
      case _ => ""
    }

    override def toString: String = {
      s"Forced evaluation of expression @ ${expr.getPos} failed because of a $error"
    }
  }
}
