/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._
import purescala.Constructors._

class ChainProcessor(
  val checker: TerminationChecker,
  val modules: ChainBuilder with ChainComparator with Strengthener with StructuralSize
) extends Processor with Solvable {

  val name: String = "Chain Processor"

  def run(problem: Problem) = {
    reporter.debug("- Strengthening postconditions")
    modules.strengthenPostconditions(problem.funSet)(this)

    reporter.debug("- Strengthening applications")
    modules.strengthenApplications(problem.funSet)(this)

    reporter.debug("- Running ChainBuilder")
    val chainsMap : Map[FunDef, (Set[FunDef], Set[Chain])] = problem.funSet.map { funDef =>
      funDef -> modules.getChains(funDef)(this)
    }.toMap

    val loopPoints = chainsMap.foldLeft(Set.empty[FunDef]) { case (set, (fd, (fds, chains))) => set ++ fds }

    if (loopPoints.size > 1) {
      reporter.debug("-+> Multiple looping points, can't build chain proof")
      None
    } else {
      val funDef = loopPoints.headOption getOrElse {
        chainsMap.collectFirst { case (fd, (fds, chains)) if chains.nonEmpty => fd }.get
      }

      val chains = chainsMap(funDef)._2

      val e1 = tupleWrap(funDef.params.map(_.toVariable))
      val e2s = chains.toSeq.map { chain =>
        val freshParams = chain.finalParams.map(arg => FreshIdentifier(arg.id.name, arg.id.getType, true))
        (chain.loop(finalArgs = freshParams), tupleWrap(freshParams.map(_.toVariable)))
      }

      reporter.debug("-+> Searching for structural size decrease")

      val structuralFormulas = modules.structuralDecreasing(e1, e2s)
      val structuralDecreasing = structuralFormulas.exists(formula => definitiveALL(formula))

      reporter.debug("-+> Searching for numerical converging")

      val numericFormulas = modules.numericConverging(e1, e2s, chains)
      val numericDecreasing = numericFormulas.exists(formula => definitiveALL(formula))

      if (structuralDecreasing || numericDecreasing)
        Some(problem.funDefs map Cleared)
      else {
        val maybeReentrant = chains.flatMap(c1 => chains.flatMap(c2 => c1 compose c2)).exists {
          chain => maybeSAT(chain.loop().toClause)
        }

        if (!maybeReentrant)
          Some(problem.funDefs map Cleared)
        else 
          None
      }
    }
  }
}
