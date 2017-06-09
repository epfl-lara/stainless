/* Copyright 2009-2016 EPFL, Lausanne */

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
  import program.trees._
  import program.symbols._

  private def lessThan(e1s: Seq[(Path, Expr)], e2: Expr): Seq[Expr] =
    flatTypesPowerset(e2.getType).toSeq.map(recons => andJoin(e1s.map {
      case (path, e1) => path implies ordering.lessThan(Seq(recons(e1)), Seq(recons(e2)))
    }))

  def run(problem: Problem) = {
    val timer = program.ctx.timers.termination.processors.chains.start()

    strengthenPostconditions(problem.funSet)
    strengthenApplications(problem.funSet)

    val api = getAPI

    reporter.debug("- Running ChainBuilder")
    val chainsMap: Map[FunDef, (Set[FunDef], Set[Chain])] = problem.funSet.map {
      funDef => funDef -> getChains(funDef)
    }.toMap

    val chainConstraints: Map[Chain, SizeConstraint] = {
      val relationConstraints: MutableMap[Relation, SizeConstraint] = MutableMap.empty

      chainsMap.flatMap { case (_, (_, chains)) =>
        chains.map(chain => chain -> {
          val constraints = chain.relations.map(relation => relationConstraints.getOrElse(relation, {
            val Relation(funDef, path, FunctionInvocation(_, _, args), _) = relation
            val args0 = funDef.params.map(_.toVariable)
            val constraint = if (api.solveVALID(path implies ordering.lessEquals(args, args0)).contains(true)) {
              if (api.solveVALID(path implies ordering.lessThan(args, args0)).contains(true)) {
                StrongDecreasing
              } else {
                WeakDecreasing
              }
            } else {
              NoConstraint
            }

            relationConstraints(relation) = constraint
            constraint
          })).toSet

          if (constraints(NoConstraint)) {
            NoConstraint
          } else if (constraints(StrongDecreasing)) {
            StrongDecreasing
          } else {
            WeakDecreasing
          }
        })
      }
    }

    val filteredChains: Map[FunDef, (Set[FunDef], Set[Chain])] = chainsMap.map { case (fd, (fds, chains)) =>
      val remainingChains = chains.filter(chain => chainConstraints(chain) != StrongDecreasing)
      fd -> ((fds, remainingChains))
    }

    val loopPoints = filteredChains.foldLeft(Set.empty[FunDef]) { case (set, (fd, (fds, chains))) => set ++ fds }

    if (loopPoints.size > 1) {
      reporter.debug("-+> Multiple looping points, can't build chain proof")
      timer.stop()
      None
    } else {
      val funDefs = if (loopPoints.nonEmpty) {
        loopPoints
      } else {
        filteredChains.collect { case (fd, (fds, chains)) if chains.nonEmpty => fd }
      }

      var cleared = false
      for (funDef <- funDefs if !cleared) {
        val chains = filteredChains(funDef)._2
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

      val res = if (cleared) {
        Some(problem.funDefs map Cleared)
      } else {
        None
      }

      timer.stop()
      res
    }
  }
}
