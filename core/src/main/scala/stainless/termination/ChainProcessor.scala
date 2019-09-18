/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap}

trait ChainProcessor extends OrderingProcessor {
  val ordering: OrderingRelation with ChainBuilder with Strengthener with StructuralSize {
    val checker: ChainProcessor.this.checker.type
  }

  val depth: Int = 1

  val name: String = "Chain Processor"

  import checker._
  import ordering._
  import checker.context._
  import checker.program.trees._
  import checker.program.symbols._

  private def lessThan(e1s: Seq[(Path, Expr)], e2: Expr): Seq[Expr] =
    flatTypesPowerset(e2.getType).toSeq.map(recons => andJoin(e1s.map {
      case (path, e1) => path implies ordering.lessThan(Seq(recons(e1)), Seq(recons(e2)))
    }))

  def run(problem: Problem) = timers.termination.processors.chains.run {
    strengthenPostconditions(problem.funSet)
    strengthenApplications(problem.funSet)

    val api = getAPI

    reporter.debug("- Running ChainBuilder")
    val chainsMap: Map[FunDef, (Set[FunDef], Set[Chain])] = problem.funSet.map {
      funDef => funDef -> getChains(funDef)
    }.toMap

    val loopPoints = chainsMap.foldLeft(Set.empty[FunDef]) { case (set, (fd, (fds, chains))) => set ++ fds }

    if (loopPoints.size > 1) {
      reporter.debug("-+> Multiple looping points, can't build chain proof")
      None
    } else {
      val funDefs = if (loopPoints.nonEmpty) {
        loopPoints
      } else {
        chainsMap.collect { case (fd, (fds, chains)) if chains.nonEmpty => fd }
      }

      var cleared = false
      for (funDef <- funDefs if !cleared) {
        val chains = chainsMap(funDef)._2
        val allChains = chainsMap(funDef)._2
        reporter.debug("- Searching for size decrease")

        val remaining = (0 to depth).foldLeft(chains) { (cs, index) =>
          reporter.debug("-+> Iteration #" + index)

          val e1s = cs.toSeq.map { chain =>
            val (path, args) = chain.loop
            (path, tupleWrap(args))
          }
          val e2 = tupleWrap(funDef.params.map(_.toVariable))

          val formulas = lessThan(e1s, e2)
          if (cleared || formulas.exists(f => api.solveVALID(f).contains(true))) {
            Set.empty
          } else {
            cs.flatMap(c1 => allChains.flatMap(c2 => c1 compose c2))
          }
        }

        cleared = remaining.isEmpty
      }

      if (cleared) Some(problem.funDefs map Cleared)
      else None
    }
  }
}
