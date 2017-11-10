/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package forceEval

import inox.evaluators.EvaluationResults._

object DebugSectionEval extends inox.DebugSection("eval")

case class ForceEvalFailedError(expr: String, msg: String) extends Exception(s"Forcing evaluation of $expr failed because $msg")

trait ForceEvaluation extends inox.ast.ProgramTransformer {

  val sourceProgram: Program
  val ctx: inox.Context

  implicit val debugSection = DebugSectionEval

  lazy val targetProgram: Program { val trees: sourceProgram.trees.type } = new inox.Program {

    val trees: sourceProgram.trees.type = sourceProgram.trees
    import trees._

    implicit val semantics = stainlessSemantics.asInstanceOf[inox.SemanticsProvider { val trees: sourceProgram.trees.type }]

    val evaluator = sourceProgram.getEvaluator(ctx)

    def forceEval(fd: FunDef): FunDef = {
      import sourceProgram.symbols._

      val toForce = exprOps.collect {
        case Force(expr) => Set(expr)
        case _ => Set.empty[Expr]
      }(fd.fullBody)

      if (toForce.isEmpty)
        return fd

      val forced = toForce map { expr =>
        ctx.reporter.debug(s"Forcing expression at ${expr.getPos}: $expr...")

        evaluator.eval(expr) match {
          case Successful(value)   =>
            ctx.reporter.debug(s" - Result: $value")
            expr -> value

          case RuntimeError(msg)   => throw ForceEvalFailedError(expr.toString, msg)
          case EvaluatorError(msg) => throw ForceEvalFailedError(expr.toString, msg)
        }
      }

      fd.copy(fullBody = exprOps.replace(forced.toMap, fd.fullBody))
    }

    val symbols = NoSymbols
      .withADTs(sourceProgram.symbols.adts.values.toSeq)
      .withFunctions(sourceProgram.symbols.functions.values.map(forceEval).toSeq)
  }

  protected object encoder extends sourceProgram.trees.IdentityTreeTransformer
  protected object decoder extends sourceProgram.trees.IdentityTreeTransformer
}

object ForceEvaluation {
  def apply(p: Program, context: inox.Context): ForceEvaluation { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
    val ctx = context
  } with ForceEvaluation
}
