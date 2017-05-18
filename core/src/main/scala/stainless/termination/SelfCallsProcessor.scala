/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import transformers.CollectorWithPC
import scala.collection.mutable.{Set => MutableSet}

trait SelfCallsProcessor extends Processor {

  val name: String = "Self Calls Processor"

  import checker._
  import program._
  import program.trees._
  import program.symbols._

  def run(problem: Problem) = {
    reporter.debug("- Self calls processor...")
    val timer = ctx.timers.termination.processors.`self-calls`.start()

    val nonTerminating = problem.funDefs
      .filter(fd => alwaysCalls(fd.fullBody, fd.id))

    val res = if (nonTerminating.nonEmpty) {
      Some(nonTerminating.map(fd => Broken(fd, LoopsGivenInputs(name, fd.params.map(_.toVariable)))))
    } else {
      None
    }

    timer.stop()
    res
  }

  private def alwaysCalls(expr: Expr, fid: Identifier): Boolean = {
    val seen: MutableSet[Identifier] = MutableSet.empty

    object collector extends CollectorWithPC {
      type Result = Boolean
      val trees: checker.program.trees.type = checker.program.trees
      val symbols: checker.program.symbols.type = checker.program.symbols

      override protected def rec(e: Expr, env: Path): Expr = e match {
        case l: Lambda => l // ignore body
        case _ => super.rec(e, env)
      }

      def step(e: Expr, pc: Path): List[Boolean] = e match {
        case FunctionInvocation(id, tps, args) if pc.isEmpty && id == fid =>
          List(true)

        case FunctionInvocation(id, tps, args) if pc.isEmpty && !seen(id) =>
          seen += id
          List(calls(getFunction(id).fullBody))

        case _ => Nil
      }
    }

    def calls(e: Expr): Boolean = collector.collect(e).foldLeft(false)(_ || _)
    calls(expr)
  }
}
