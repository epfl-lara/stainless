/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
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
    val chainsMap: Map[FunDef, (Set[FunDef], Set[Chain])] = problem.funSet.map { funDef =>
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

        val decreases = formulas.find { f =>
          println(f._1.asString(PrinterOptions.fromContext(context)))
          val res = api.solveVALID(f._1)
          println(res)
          res.contains(true)
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
        val induced = buildDecreases(MeasureRegister.getOrElse(fd, Set()).toList)
        induced match {
          case Some(measure) =>
            measureCache.add(fd -> measure)
            Cleared(fd, Some(measure))
          case None =>
            throw FailedMeasureInference(fd,
              "No measure annotated in function: " + fd.id + " which was cleared in chain processor.")
        }
      })
    } else {
      None
    }
  }

  /*
    Measure annotation for the chain processor
   */

  // register holding all measures deduced for a function.
  // instead of a value List we can put Set to avoid repetitions
  // (if don't care about efficiency).
  //
  // again this seems to do with concurrency
  private object MeasureRegister {
    private val cache: MutableMap[FunDef, MutableSet[(Path, Expr)]] = MutableMap.empty

    def add(fd: FunDef, path: Path, measure: Expr) = {
      cache.get(fd) match {
        case Some(s) => cache.update(fd, s += (path -> measure))
        case None    => cache += (fd -> MutableSet((path, measure)))
      }
    }

    def get(fd: FunDef) = cache.get(fd)
    def getOrElse(fd: FunDef, elze: => Set[(Path, Expr)]) = cache.getOrElse(fd, elze)
  }

  // Registers the function annotated, the path condition and the measure contribution of this branch
  private def annotate(chains: Set[Chain], fd: FunDef, recons: Expr => Expr): Unit = {

    def writeMeasure(r: Relation, chain: Chain, index: Int, first: Boolean) = {
      val (bPath, bArgs) = chain.loop
      val (path, args) = (r.path, if (first) r.fd.params.map(_.toVariable) else bArgs)
      val induced = ordering.measure(Seq(recons(tupleWrap(args))))
      val measure = {
        val templateMeasure = flatten(induced, Seq(IntegerLiteral(index)))
        if (first) templateMeasure else bindingsToLets(bPath.bindings, templateMeasure)
      }
      MeasureRegister.add(r.fd, path, measure)
    }

    @annotation.tailrec
    def rec(chain: Chain, index: Int): Unit = chain.relations match {
      case r :: Nil => writeMeasure(r, chain, index, false); ()
      case r :: rs  => writeMeasure(r, chain, index, false); rec(Chain(rs), index - 1)
      case Nil      => ()
    }

    val newChains = chains.map { chain =>
      val (start, end) = chain.relations.splitAt(chain.relations.map(_.fd.id).indexOf(fd.id))
      Chain(end ++ start)
    }

    newChains.map { chain =>
      writeMeasure(chain.relations.head, chain, 0, true)
      rec(Chain(chain.relations.tail), chain.size - 1)
    }
  }

  private def buildDecreases(l: List[(Path, Expr)]) = {
    @annotation.tailrec
    def rec(acc: Expr, l: List[(Path, Expr)]): Expr = l match {
      case (p, e) :: t => rec(IfExpr(p.toClause, e, acc), t)
      case Nil         => acc
    }

    l match {
      case Nil                  => None
      case (path, expr) :: rest =>
        Some(rec(IfExpr(path.toClause, expr, zeroTuple(expr)), rest))
    }
  }

}
