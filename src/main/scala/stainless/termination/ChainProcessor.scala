/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

trait ChainProcessor extends OrderingProcessor {
  val ordering: OrderingRelation with ChainBuilder with Strengthener with StructuralSize {
    val checker: ChainProcessor.this.checker.type
  }

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
    strengthenPostconditions(problem.funSet)
    strengthenApplications(problem.funSet)

    reporter.debug("- Running ChainBuilder")
    val chainsMap : Map[FunDef, (Set[FunDef], Set[Chain])] = problem.funSet.map {
      funDef => funDef -> getChains(funDef)
    }.toMap

    val loopPoints = chainsMap.foldLeft(Set.empty[FunDef]) { case (set, (fd, (fds, chains))) => set ++ fds }

    if (loopPoints.size > 1) {
      reporter.debug("-+> Multiple looping points, can't build chain proof")
      None
    } else {
      val funDef = loopPoints.headOption getOrElse {
        chainsMap.collectFirst { case (fd, (fds, chains)) if chains.nonEmpty => fd }.getOrElse {
          reporter.fatalError("Couldn't find chain set")
        }
      }

      val chains = chainsMap(funDef)._2

      val e1s = chains.toSeq.map { chain =>
        val freshParams = chain.finalParams.map(_.freshen)
        (chain.loop(finalArgs = freshParams), tupleWrap(freshParams.map(_.toVariable)))
      }
      val e2 = tupleWrap(funDef.params.map(_.toVariable))

      reporter.debug("-+> Searching for size decrease")

      val formulas = lessThan(e1s, e2)
      if (formulas.exists(f => solveVALID(f).contains(true))) {
        Some(problem.funDefs map Cleared)
      } else {
        val maybeReentrant = chains.flatMap(c1 => chains.flatMap(c2 => c1 compose c2)).exists {
          chain => !solveSAT(chain.loop().toClause).isUNSAT
        }

        if (!maybeReentrant)
          Some(problem.funDefs map Cleared)
        else 
          None
      }
    }
  }
}
