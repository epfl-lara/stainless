package leon
package termination

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

class LoopProcessor(checker: TerminationChecker, k: Int = 10) extends Processor(checker) with Solvable {

  val name: String = "Loop Processor"

  def run(problem: Problem) = {
    val allChains : Set[Chain] = problem.funDefs.map(fd => ChainBuilder.run(fd)).flatten
    // Get reentrant loops (see ChainProcessor for more details)
    val chains    : Set[Chain] = allChains.filter(chain => !solve(Not(And(chain reentrant chain))).isValid)

    def findLoops(chains: Set[Chain]) = {
      def rec(chains: Set[Chain], count: Int): Map[FunDef, Seq[Expr]] = if (count == k) Map() else {
        val nonTerminating = chains.flatMap({ chain =>
          val freshArgs : Seq[Expr] = chain.funDef.args.map(arg => arg.id.freshen.toVariable)
          val finalBindings = (chain.funDef.args.map(_.id) zip freshArgs).toMap
          val path = chain.times(count, finalSubst = finalBindings)
          val formula = And(path :+ Equals(Tuple(chain.funDef.args.map(_.toVariable)), Tuple(freshArgs)))

          val solvable = functionCallsOf(formula).forall({
            case FunctionInvocation(fd, args) => checker.terminates(fd).isGuaranteed
          })

          if (!solvable) None else solve(Not(formula)) match {
            case Solution(false, model) => Some(chain.funDef, chain.funDef.args.map(arg => model(arg.id)))
            case _ => None
          }
        }).toMap

        val remainingChains = chains.filter(chain => nonTerminating.contains(chain.funDef))
        nonTerminating ++ rec(remainingChains, count + 1)
      }

      rec(chains, 1)
    }

    val nonTerminating = findLoops(chains)
    val results = nonTerminating.map({ case (funDef, args) => Broken(funDef, args) })
    val remaining = problem.funDefs -- nonTerminating.keys
    val newProblems = if (remaining.nonEmpty) List(Problem(remaining)) else Nil
    (results, newProblems)
  }
}

// vim: set ts=4 sw=4 et:
