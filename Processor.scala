/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._

import scala.concurrent.duration._

import leon.solvers._

trait Processor {

  val name: String

  val checker : TerminationChecker

  implicit val debugSection = utils.DebugSectionTermination
  val reporter = checker.context.reporter

  def run(problem: Problem): Option[Seq[Result]]
}

trait Solvable extends Processor {

  val modules: Strengthener with StructuralSize

  private val solver: SolverFactory[Solver] =
    SolverFactory.getFromSettings(checker.context, checker.program).withTimeout(1.seconds)

  type Solution = (Option[Boolean], Map[Identifier, Expr])

  private def withoutPosts[T](block: => T): T = {
    val dangerousFunDefs = checker.functions.filter(fd => !checker.terminates(fd).isGuaranteed)
    val backups = dangerousFunDefs.toList map { fd =>
      val p = fd.postcondition
      fd.postcondition = None
      () => fd.postcondition = p
    }

    val res : T = block // force evaluation now
    backups.foreach(_())
    res
  }

  def maybeSAT(problem: Expr): Boolean = withoutPosts {
    SimpleSolverAPI(solver).solveSAT(problem)._1 getOrElse true
  }

  def definitiveALL(problem: Expr): Boolean = withoutPosts {
    SimpleSolverAPI(solver).solveSAT(Not(problem))._1.exists(!_)
  }

  def definitiveSATwithModel(problem: Expr): Option[Model] = withoutPosts {
    val (sat, model) = SimpleSolverAPI(solver).solveSAT(problem)
    if (sat.isDefined && sat.get) Some(model) else None
  }
}

