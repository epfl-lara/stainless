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
                        (override val ordering: OrderingRelation with ChainBuilder with Strengthener with StructuralSize {
                          val checker: chker.type
                        })
  extends OrderingProcessor("Decreases Processor", checker, ordering) {

  def this(chker: ProcessingPipeline,
           ordering: OrderingRelation with ChainBuilder with Strengthener with StructuralSize {
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

    def rec(fd: FunDef, seen: Set[FunDef]): Unit = {

      if (!problem.funSet(fd) || !MeasureRegister.get(fd).isEmpty) {
        // Nothing to do
      } else if (fd.measure.isDefined) {
        // Here we start at one to avoid (0,0) > (0,0) that happen for instance in PackratParsing
        MeasureRegister.add(fd, None, fd.measure.get, 1)
        val flat = flatten(fd.measure.get, Seq(IntegerLiteral(1)))
        MeasureRegister.addMeasure(fd, flat)
      } else if (seen(fd)) {
        // Fail, non-annotated cycle detected
        throw FailedMeasureInference(fd, "Cycle without measure detected for: " + fd.id)
      } else {
        // Look for decreases and annotate measures in register
        val calls = collectForConditions[(FunctionInvocation, Path)] {
          case (fi: FunctionInvocation, path: Path) => (fi, path)
        }(fd.fullBody)

        // Add all the decreases of this function
        calls.map {
          case (fi, path) =>
            val target = fi.tfd.fd
            rec(target, seen + target)

            MeasureRegister.get(target).map {
              case (oRel, oExpr, oIndex) =>
                val nCall = Relation(fd, path, fi, false) // for now we don't need inLambda
                val rel = oRel match { case Some(r) => nCall compose r; case None => nCall }
                val freshParams = rel.call.tfd.params.map(_.freshen)
                val fullPath = rel.path withBindings (freshParams zip rel.call.args)
                val subst: Map[ValDef, Expr] = (rel.call.tfd.params zip freshParams.map(_.toVariable)).toMap
                val oExprP = exprOps.replaceFromSymbols(subst, oExpr)
                val (nRel, nExpr, nIndex) = (Some(rel), bindingsToLets(fullPath.bindings, oExprP), oIndex + 1)
                MeasureRegister.add(fd, nRel, nExpr, nIndex)
            }
        }

        if (MeasureRegister.has(fd)) {
          MeasureRegister.addMeasure(fd, buildMeasure(MeasureRegister.get(fd).toList))
        }
      }

    }

    fds.map(fd => rec(fd, Set())) // probably accumulate the already seen functions
  }

  /*
    If measures is empty the node already has an annotated decrease.
    In that case, rewrite the decrease to a tuple.
    If measures isn't empty gather the different measures into an ifexpr
    increasing the index by one.
   */

  def buildMeasure(measures: List[(Option[Relation], Expr, BigInt)]): Expr = {
    require(measures.nonEmpty)

    @annotation.tailrec
    def rec(builtIf: Expr, measures: List[(Option[Relation], Expr, BigInt)]): Expr = measures match {
      case (rel, expr, index) :: rest =>
        val path = rel match { case Some(r) => r.path; case None => Path.empty }
        val measure = flatten(expr, Seq(IntegerLiteral(index)))
        rec(IfExpr(path.toClause, expr, builtIf), rest)
      case Nil =>
        builtIf
    }

    val (rel, expr, index) :: rest = measures // safe because of precondition

    val path = rel match { case Some(r) => r.path; case None => Path.empty }
    val flat = flatten(expr, Seq(IntegerLiteral(index)))
    val baseIf = IfExpr(path.toClause, flat, zeroTuple(flat))
    rec(baseIf, rest)
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
