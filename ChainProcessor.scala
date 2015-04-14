/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._
import purescala.Constructors.tupleWrap

class ChainProcessor(val checker: TerminationChecker with ChainBuilder with ChainComparator with Strengthener with StructuralSize) extends Processor with Solvable {

  val name: String = "Chain Processor"

  def run(problem: Problem) = {
    reporter.debug("- Strengthening postconditions")
    checker.strengthenPostconditions(problem.funDefs)(this)

    reporter.debug("- Strengthening applications")
    checker.strengthenApplications(problem.funDefs)(this)

    reporter.debug("- Running ChainBuilder")
    val chainsMap : Map[FunDef, (Set[FunDef], Set[Chain])] = problem.funDefs.map { funDef =>
      funDef -> checker.getChains(funDef)(this)
    }.toMap

    val loopPoints = chainsMap.foldLeft(Set.empty[FunDef]) { case (set, (fd, (fds, chains))) => set ++ fds }

    if (loopPoints.size > 1) {
      reporter.debug("-+> Multiple looping points, can't build chain proof")
      (Nil, List(problem))
    } else {

      def exprs(fd: FunDef): (Expr, Seq[(Seq[Expr], Expr)], Set[Chain]) = {
        val fdChains = chainsMap(fd)._2

        val e1 = tupleWrap(fd.params.map(_.toVariable))
        val e2s = fdChains.toSeq.map { chain =>
          val freshParams = chain.finalParams.map(arg => FreshIdentifier(arg.id.name, arg.id.getType, true))
          (chain.loop(finalArgs = freshParams), tupleWrap(freshParams.map(_.toVariable)))
        }

        (e1, e2s, fdChains)
      }

      val funDefs = if (loopPoints.size == 1) Set(loopPoints.head) else problem.funDefs

      reporter.debug("-+> Searching for structural size decrease")

      val (se1, se2s, _) = exprs(funDefs.head)
      val structuralFormulas = checker.structuralDecreasing(se1, se2s)
      val structuralDecreasing = structuralFormulas.exists(formula => definitiveALL(formula))

      reporter.debug("-+> Searching for numerical converging")

      // worth checking multiple funDefs as the endpoint discovery can be context sensitive
      val numericDecreasing = funDefs.exists { fd =>
        val (ne1, ne2s, fdChains) = exprs(fd)
        val numericFormulas = checker.numericConverging(ne1, ne2s, fdChains)
        numericFormulas.exists(formula => definitiveALL(formula))
      }

      if (structuralDecreasing || numericDecreasing) {
        (problem.funDefs.map(Cleared), Nil)
      } else {
        (Nil, List(problem))
      }
    }
  }
}
