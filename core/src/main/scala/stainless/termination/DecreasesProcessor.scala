/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._
import scala.annotation.tailrec
import solvers._

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

/**
  * Checks terminations of functions using the ranking function specified in the `decreases`
  * construct. For now, it works only on first-order functions.
  */
class DecreasesProcessor(override val checker: ProcessingPipeline)
                        // Alias for checker, as we cannot use it to define ordering
                        (override val chker: checker.type)
                        (override val ordering: OrderingRelation & ChainBuilder & Strengthener & StructuralSize {
                          val checker: chker.type
                        })
  extends OrderingProcessor("Decreases Processor", checker, ordering) {

  def this(chker: ProcessingPipeline,
           ordering: OrderingRelation & ChainBuilder & Strengthener & StructuralSize {
             val checker: chker.type
           }) =
    this(chker)(chker)(ordering)

  import ordering._
  import checker._
  import checker.context._
  import checker.program._
  import checker.program.trees._
  import checker.program.symbols.{given, _}
  import checker.program.trees.exprOps._

  // redo the checks for termination of functions in the measure
  def run(problem: Problem): Option[Seq[Result]] = timers.termination.processors.decreases.run {
    val fds = problem.funDefs

    if (fds.exists { _.measure.isDefined }) {
      checkMeasures(problem)
      annotateGraph(problem) // should fail internally if not all can be annotated
      val inductiveLemmas = 
        Some((ordering.getPostconditions, ordering.insertedApps))
      Some(fds.map(fd => Cleared(fd, MeasureRegister.getMeasure(fd), inductiveLemmas)))
    } else {
      None
    }
  }

  // (a) check if every function in the measure terminates
  // and does not make a recursive call to an SCC.
  private def checkMeasures(problem: Problem) = {
    val fds = problem.funDefs
    val fdIds = problem.funSet.map(_.id)

    fds.filter(_.measure.isDefined).forall { fd =>
      val measure = fd.measure.get
      !exists {
        case FunctionInvocation(id, _, _) =>
          if (fdIds(id)) {
            throw FailedMeasureInference(fd, s"`decreases` has recursive call to ${id.name}.")
            true
          } else if (!checker.terminates(getFunction(id)).isGuaranteed) {
            throw FailedMeasureInference(fd, s"`decreases` calls non-terminating function ${id.name}.")
            true
          } else {
            false
          }
        case _ =>
          false
      }(measure)
    }
  }

  /*
    Measure annotation
   */

  private object MeasureRegister {
    // change cache to contain only idenfier
    private val cache: MutableMap[FunDef, Set[(Option[Relation], Expr, BigInt)]] = MutableMap.empty
    private val measures: MutableMap[FunDef, Expr] = MutableMap.empty
    def add(fd: FunDef, r: Option[Relation], measure: Expr, index: BigInt) = cache.get(fd) match {
      case Some(s) => cache.update(fd, s + ((r, measure, index)))
      case None    => cache += (fd -> Set((r, measure, index)))
    }
    def has(fd: FunDef): Boolean = get(fd).nonEmpty
    def get(fd: FunDef): Set[(Option[Relation], Expr, BigInt)] = cache.get(fd) match {
      case Some(s) => s
      case None    => Set.empty
    }
    def addMeasure(fd: FunDef, measure: Expr): Unit = measures += fd -> measure
    def getMeasure(fd: FunDef): Option[Expr] = measures.get(fd)
  }

  private def annotateGraph(problem: Problem) = {
    val fds = problem.funDefs
    val ids = problem.funSet.map(_.id)
    val updatedSymbols = apiTransform(checker.program.symbols)

    def components(measure: Expr): Seq[Expr] = measure.getType(using updatedSymbols) match {
      case TupleType(_) => unwrapTuple(measure, true)(using updatedSymbols)
      case _            => Seq(measure)
    }

    // The measures of the problem must have the same type: the components of the longest annotated measure (the
    // shorter ones are padded with zeros), followed by an index. The index of the annotated functions exceeds the
    // floors of the functions without measure (see below), which are smaller than the number of such functions.
    val longest = fds.flatMap(_.measure).maxBy(components(_).size)
    val index = BigInt(fds.count(_.measure.isEmpty) max 1)

    def lift(measure: Expr, i: BigInt): Expr =
      flatten(measure, components(longest).drop(components(measure).size).map(zeroTuple) :+ IntegerLiteral(i))

    // The bindings of `path` that `e` depends on
    def bindingsOf(path: Path, e: Expr): Seq[(ValDef, Expr)] =
      path.bindings.foldRight((Seq.empty[(ValDef, Expr)], exprOps.variablesOf(e))) {
        case ((vd, v), (bindings, vars)) if vars(vd.toVariable) => ((vd, v) +: bindings, vars ++ exprOps.variablesOf(v))
        case (_, acc)                                         => acc
      }._1

    // Measures cannot call the functions of the problem: drops the parts of the path that depend on such calls
    def withoutCalls(path: Path): Path = {
      var dropped = Set.empty[Variable]
      def dependsOnCalls(e: Expr) = exprOps.variablesOf(e).exists(dropped) || exists {
        case FunctionInvocation(id, _, _) => ids(id)
        case _                            => false
      }(e)
      Path(path.elements.filter {
        case Path.CloseBound(vd, e) if dependsOnCalls(e) => dropped += vd.toVariable; false
        case Path.Condition(e)                           => !dependsOnCalls(e)
        case _                                           => true
      })
    }

    // The lexicographic maximum of two measures
    def max(m1: Expr, m2: Expr): Expr = {
      val v1 = ValDef.fresh("measure", m1.getType(using updatedSymbols))
      val v2 = ValDef.fresh("measure", m2.getType(using updatedSymbols))
      val smaller =
        lexicographicallySmaller(components(v1.toVariable), components(v2.toVariable), strict = true, e => e)
      Let(v1, m1, Let(v2, m2, IfExpr(smaller, v2.toVariable, v1.toVariable)))
    }

    def rec(fd: FunDef, seen: Set[FunDef]): Unit = {

      if (!problem.funSet(fd) || !MeasureRegister.get(fd).isEmpty) {
        // Nothing to do
      } else if (fd.measure.isDefined) {
        MeasureRegister.add(fd, None, fd.measure.get, index)
        MeasureRegister.addMeasure(fd, lift(fd.measure.get, index))
      } else if (seen(fd)) {
        // Fail, non-annotated cycle detected
        throw FailedMeasureInference(fd, "Cycle without measure detected for: " + fd.id)
      } else {
        // Look for decreases and annotate measures in register
        val calls = collectForConditions[(FunctionInvocation, Path)] {
          case (fi: FunctionInvocation, path: Path) if ids(fi.id) => (fi, path)
        }(fd.fullBody)

        // Add all the decreases of this function
        calls.map {
          case (fi, path) =>
            val target = fi.tfd.fd
            rec(target, seen + fd)

            MeasureRegister.get(target).map {
              case (oRel, oExpr, oIndex) =>
                val nCall = Relation(fd, path, fi, false) // for now we don't need inLambda
                val rel = oRel match { case Some(r) => nCall `compose` r; case None => nCall }
                // `oExpr` is in terms of the parameters of `target`
                val freshParams = fi.tfd.params.map(_.freshen)
                val fullPath = path `withBindings` (freshParams zip fi.args)
                val subst: Map[ValDef, Expr] = (fi.tfd.params zip freshParams.map(_.toVariable)).toMap
                val oExprP = exprOps.replaceFromSymbols(subst, fi.tfd.instantiate(oExpr))
                val (nRel, nExpr, nIndex) =
                  (Some(rel), bindingsToLets(bindingsOf(fullPath, oExprP), oExprP), oIndex + 1)
                MeasureRegister.add(fd, nRel, nExpr, nIndex)
            }
        }

        // The measure of `fd` is the maximum of the measures of the calls on the current path (whose index grows with
        // the length of the chain of calls to an annotated function) and of a floor, which exceeds the floors of the
        // functions without measure that `fd` calls
        if (MeasureRegister.has(fd)) {
          val measures = MeasureRegister.get(fd).toList
          val floor = lift(zeroTuple(longest), measures.map(_._3).max - index - 1)
          MeasureRegister.addMeasure(fd, measures.map {
            case (rel, expr, i) => IfExpr(withoutCalls(rel.get.path).toClause, lift(expr, i), floor)
          }.reduce(max))
        }
      }

    }

    fds.map(fd => rec(fd, Set())) // probably accumulate the already seen functions
  }

  /*
    Utils
   */

  protected def collectForConditions[T](pf: PartialFunction[(Expr, Path), T])(e: Expr): Seq[T] = {
    val results: ListBuffer[T] = new ListBuffer
    val lifted = pf.lift

    transformWithPC(e)((e, path, op) =>
      e match {
        case Annotated(_, flags) if flags contains DropVCs => e
        case _ =>
          lifted(e, path).foreach(results += _)
          op.sup(e, path)
      }
    )

    results.toList
  }
}
