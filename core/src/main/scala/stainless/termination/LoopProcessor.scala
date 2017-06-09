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

  object withoutPosts extends inox.ast.SimpleSymbolTransformer {
    val s: program.trees.type = program.trees
    val t: program.trees.type = program.trees

    protected def transformFunction(fd: FunDef): FunDef =
      fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, None))

    protected def transformADT(adt: ADTDefinition): ADTDefinition = adt
  }

  def run(problem: Problem) = {
    val timer = program.ctx.timers.termination.processors.loops.start()

    strengthenApplications(problem.funSet)
    val api = getAPI(withoutPosts)

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

          api.solveSAT(path and equality(srcTuple, resTuple)) match {
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

    val res = if (nonTerminating.nonEmpty) {
      Some(nonTerminating.values.toSeq)
    } else {
      None
    }

    timer.stop()
    res
  }
}
