/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._
import purescala.Common._
import purescala.Expressions._
import purescala.Constructors._

import scala.collection.mutable.{Map => MutableMap}

class LoopProcessor(val checker: TerminationChecker, val modules: ChainBuilder with Strengthener with StructuralSize, k: Int = 10) extends Processor with Solvable {

  val name: String = "Loop Processor"

  def run(problem: Problem) = {
    reporter.debug("- Strengthening applications")
    modules.strengthenApplications(problem.funSet)(this)

    reporter.debug("- Running ChainBuilder")
    val chains : Set[Chain] = problem.funSet.flatMap(fd => modules.getChains(fd)(this)._2)

    reporter.debug("- Searching for loops")
    val nonTerminating: MutableMap[FunDef, Result] = MutableMap.empty

    (0 to k).foldLeft(chains) { (cs, index) =>
      reporter.debug("-+> Iteration #" + index)
      for (chain <- cs if !nonTerminating.isDefinedAt(chain.funDef) &&
          (chain.funDef.params zip chain.finalParams).forall(p => p._1.getType == p._2.getType)) {
        val freshParams = chain.funDef.params.map(arg => FreshIdentifier(arg.id.name, arg.getType, true))
        val path = chain.loop(finalArgs = freshParams)

        val srcTuple = tupleWrap(chain.funDef.params.map(_.toVariable))
        val resTuple = tupleWrap(freshParams.map(_.toVariable))

        definitiveSATwithModel(andJoin(path :+ Equals(srcTuple, resTuple))) match {
          case Some(model) =>
            val args = chain.funDef.params.map(arg => model(arg.id))
            val res = if (chain.relations.exists(_.inLambda)) MaybeBroken(chain.funDef, args) else Broken(chain.funDef, args)
            nonTerminating(chain.funDef) = res
          case None =>
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
