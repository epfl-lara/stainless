/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap}

class LoopProcessor(override val checker: ProcessingPipeline)
                   // Alias for checker, as we cannot use it to define ordering
                   (override val chker: checker.type)
                   (override val ordering: OrderingRelation with ChainBuilder with Strengthener {
                     val checker: chker.type
                   })
  extends OrderingProcessor("Loop Processor", checker, ordering) {

  def this(chker: ProcessingPipeline,
           ordering: OrderingRelation with ChainBuilder with Strengthener {
             val checker: chker.type
           }) =
    this(chker)(chker)(ordering)

  val depth: Int = 2

  import checker._
  import ordering._
  import checker.context._
  import checker.program.trees._
  import checker.program.symbols.{given, _}

  class WithoutPosts(override val s: program.trees.type, override val t: program.trees.type)
    extends inox.transformers.SimpleSymbolTransformer {

    protected def transformFunction(fd: FunDef): FunDef =
      fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, None)).copiedFrom(fd)

    protected def transformSort(sort: ADTSort): ADTSort = sort
  }
  val withoutPosts = new WithoutPosts(program.trees, program.trees)

  def run(problem: Problem) = timers.termination.processors.loops.run {
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
              val fi = chain.fd.typed.applied(args)
              nonTerminating(chain.fd) = Broken(chain.fd,
                if (chain.relations.exists(_.inLambda)) MaybeLoopsGivenInputs(fi)
                else LoopsGivenInputs(fi)
              )
            case _ =>
          }
        }
      }

      cs.flatMap(c1 => chains.flatMap(c2 => c1.compose(c2)))
    }

    if (nonTerminating.nonEmpty) Some(nonTerminating.values.toSeq)
    else None
  }
}
