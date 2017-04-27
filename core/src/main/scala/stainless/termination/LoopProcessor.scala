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
      for (chain <- cs if !nonTerminating.isDefinedAt(chain.fd)) {
        val (path, args) = chain.loop
        if ((chain.fd.params zip args).forall { case (vd, arg) => isSubtypeOf(arg.getType, vd.tpe) }) {
          val srcTuple = tupleWrap(chain.fd.params.map(_.toVariable))
          val resTuple = tupleWrap(args)

          solveSAT(path and equality(srcTuple, resTuple)) match {
            case inox.solvers.SolverResponses.SatWithModel(model) =>
              val args = chain.fd.params.map(vd => model.vars(vd))
              nonTerminating(chain.fd) = Broken(chain.fd,
                if (chain.relations.exists(_.inLambda)) MaybeLoopsGivenInputs(name, args)
                else LoopsGivenInputs(name, args)
              )
            case _ =>
          }
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
