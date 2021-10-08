/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Set => MutableSet}

class SelfCallsProcessor(chker: ProcessingPipeline) extends Processor("Self Calls Processor", chker) {
  import checker._
  import checker.context._
  import checker.program._
  import checker.program.trees._
  import checker.program.symbols.{given, _}

  def run(problem: Problem) = timers.termination.processors.`self-calls`.run {
    reporter.debug("- Self calls processor...")

    val nonTerminating = problem.funDefs
      .filter(fd => alwaysCalls(fd.fullBody, fd.id))

    if (nonTerminating.nonEmpty) {
      Some(nonTerminating.map(fd => Broken(fd, LoopsGivenInputs(fd.typed.applied))))
    } else {
      None
    }
  }

  private def alwaysCalls(expr: Expr, fid: Identifier): Boolean = {
    val seen: MutableSet[Identifier] = MutableSet.empty
    var result: Boolean = false

    transformWithPC(expr)((e, path, op) => e match {
      case l: Lambda => l
      case _ if !path.isEmpty || result => e
      case fi: FunctionInvocation =>
        if (path.isEmpty && fi.id == fid) result = true
        else if (path.isEmpty && !seen(fi.id)) {
          seen += fi.id
          op(getFunction(fi.id).fullBody, path)
        }
        op.sup(e, path)
      case _ => op.sup(e, path)
    })

    result
  }
}
