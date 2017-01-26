/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap}

trait LoopProcessor extends OrderingProcessor {

  val ordering: OrderingRelation with ChainBuilder with Strengthener {
    val checker: LoopProcessor.this.checker.type
  }

  val depth: Int = 2

  val name: String = "Loop Processor"

  import checker._
  import ordering._
  import program.trees._
  import program.symbols._

  def run(problem: Problem) = {
    strengthenApplications(problem.funSet)

    reporter.debug("- Running ChainBuilder")
    val chains : Set[Chain] = problem.funSet.flatMap(fd => getChains(fd)._2)

    reporter.debug("- Searching for loops")
    val nonTerminating: MutableMap[FunDef, Result] = MutableMap.empty

    (0 to depth).foldLeft(chains) { (cs, index) =>
      reporter.debug("-+> Iteration #" + index)
      for (chain <- cs if !nonTerminating.isDefinedAt(chain.fd) &&
          (chain.fd.params zip chain.finalParams).forall(p => p._1.getType == p._2.getType)) {
        val freshParams = chain.fd.params.map(_.freshen)
        val path = chain.loop(finalArgs = freshParams)

        val srcTuple = tupleWrap(chain.fd.params.map(_.toVariable))
        val resTuple = tupleWrap(freshParams.map(_.toVariable))

        solveSAT(path and equality(srcTuple, resTuple)) match {
          case inox.solvers.SolverResponses.SatWithModel(model) =>
            val args = chain.fd.params.map(vd => model.vars(vd))
            val res = if (chain.relations.exists(_.inLambda)) MaybeBroken(chain.fd, args) else Broken(chain.fd, args)
            nonTerminating(chain.fd) = res
          case _ =>
        }
      }

      cs.flatMap(c1 => chains.flatMap(c2 => c1.compose(c2)))
    }

    if (nonTerminating.nonEmpty)
      Some(nonTerminating.values.toSeq)
    else
      None
  }
}

// vim: set ts=4 sw=4 et:
