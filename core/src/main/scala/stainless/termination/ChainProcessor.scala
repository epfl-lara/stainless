/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import scala.language.existentials
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

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

  private def lessThan(e1s: Seq[(Path, Expr)], e2: Expr): Seq[(Expr, Expr, Expr => Expr)] =
    flatTypesPowerset(e2.getType).toSeq.map(recons => (andJoin(e1s.map {
      case (path, e1) => path implies ordering.lessThan(Seq(recons(e1)), Seq(recons(e2)))
    }), recons(e2), recons))

  def run(problem: Problem): Option[Seq[Result]] = timers.termination.processors.chains.run {
    strengthenPostconditions(problem.funSet)
    strengthenApplications(problem.funSet)

    val api = getAPI

    reporter.debug("- Running ChainBuilder")
    val chainsMap = problem.funSet.map { funDef =>
      funDef -> getChains(funDef)
    }.toMap

    val loopPoints = chainsMap.foldLeft(Set.empty[FunDef]) {
      case (set, (fd, (fds, chains))) => set ++ fds
    }

    if (loopPoints.size > 1) {
      reporter.debug("-+> Multiple looping points, can't build chain proof")
      return None
    }

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
        val decreases = formulas.find { case (query, _, _) =>
          api.solveVALID(query).contains(true)
        }

        if (cleared || decreases.isDefined) {
          annotate(cs, funDef, decreases.get._3)
          Set.empty
        } else {
          cs.flatMap(c1 => allChains.flatMap(c2 => c1 compose c2))
        }
      }

      cleared = remaining.isEmpty
    }

    if (cleared) {
      Some(problem.funDefs.map { fd =>
        val induced = buildDecreases(fd, MeasureRegister.getOrElse(fd, Set.empty).toList)
        induced match {
          case Some(measure) =>
            measureCache.add(fd -> measure)
            Cleared(fd, Some(measure))
          case None =>
            throw FailedMeasureInference(fd,
              s"No measure annotated in function `${fd.id}` which was cleared in chain processor.")
        }
      })
    } else {
      None
    }
  }

  /*
   * Measure annotation for the chain processor
   */

  /** Register holding all measures deduced for a function. */
  private object MeasureRegister {
    private val cache: MutableMap[FunDef, MutableSet[(Int, Expr)]] = MutableMap.empty

    def add(fd: FunDef, index: Int, measure: Expr) = {
      cache.get(fd) match {
        case Some(s) => cache.update(fd, s += (index -> measure))
        case None    => cache += (fd -> MutableSet(index -> measure))
      }
    }

    def get(fd: FunDef) = cache.get(fd)
    def getOrElse(fd: FunDef, elze: => Set[(Int, Expr)]) = cache.getOrElse(fd, elze)
  }

  def simplify(e: Expr) = {
    exprOps.postMap({
      case Let(vd, a @ Annotated(ADTSelector(v: Variable, _), Seq(Unchecked)), b) =>
        Some(exprOps.replaceFromSymbols(Map(vd -> a), b))
      case _ =>
        None
    }, applyRec = true)(e)
  }

  /** Registers the function annotated, the path condition and the measure contribution of this branch */
  private def annotate(chains: Set[Chain], fd: FunDef, recons: Expr => Expr): Unit = {
    def writeMeasure(chain: Chain) = {
      val (path, args) = chain.loop

      for ((rel, index) <- chain.relations.zipWithIndex) {
        val induced = ordering.measure(Seq(recons(tupleWrap(rel.call.args))))
        val measure = simplify(bindingsToLets(rel.path.bindings, induced))
        val guarded = IfExpr(simplify(rel.path.toClause), measure, IntegerLiteral(0))

        MeasureRegister.add(fd, index, guarded)
      }
    }

    chains.foreach(writeMeasure)
  }

  private def buildDecreases(fd: FunDef, stages: List[(Int, Expr)]): Option[Expr] = {
    if (stages.isEmpty) return None

    val measures = stages
      .groupBy(_._1)
      .mapValues(_.map(_._2))
      .toList
      .sortBy(_._1)
      .map(_._2)
      .map(Max(_))

    val induced = ordering.measure(Seq(tupleWrap(fd.params.map(_.toVariable))))
    val decreases = measures.foldLeft(induced)(Plus(_, _))

    Some(decreases)
  }
}
