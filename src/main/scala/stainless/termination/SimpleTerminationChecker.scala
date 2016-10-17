/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import utils._

import scala.collection.mutable.{ Map => MutableMap }

import scala.annotation.tailrec

class SimpleTerminationChecker(context: LeonContext, program: Program) extends TerminationChecker(context, program) {

  val name = "T1"
  val description = "The simplest form of Terminator™"

  private lazy val callGraph: Map[FunDef, Set[FunDef]] =
    program.callGraph.allCalls.groupBy(_._1).mapValues(_.map(_._2)) // one liner from hell

  private lazy val components = SCC.scc(callGraph)
  val allVertices = callGraph.keySet ++ callGraph.values.flatten

  val sccArray = components.toArray
  val cSize = sccArray.length

  val funDefToSCCIndex = (callGraph.keySet ++ callGraph.values.flatten).map(v =>
    v -> (0 until cSize).find(i => sccArray(i)(v)).get).toMap

  val sccGraph = (0 until cSize).map({ i =>
    val dsts = for {
      v <- sccArray(i)
      c <- callGraph.getOrElse(v, Set.empty)
    } yield funDefToSCCIndex(c)
    i -> dsts
  }).toMap

  private val answerCache = MutableMap.empty[FunDef, TerminationGuarantee]

  def terminates(funDef: FunDef) = answerCache.getOrElse(funDef, {
    val g = forceCheckTermination(funDef)
    answerCache(funDef) = g
    g
  })

  private def forceCheckTermination(funDef: FunDef): TerminationGuarantee = {
    // We would have to clarify what it means to terminate.
    // We would probably need something along the lines of:
    //   "Terminates for all values satisfying prec."
    if (funDef.hasPrecondition)
      return NoGuarantee

    // This is also too confusing for me to think about now.
    if (!funDef.hasBody)
      return NoGuarantee

    val sccIndex = funDefToSCCIndex.getOrElse(funDef, {
      return NoGuarantee
    })
    val sccCallees = sccGraph(sccIndex)

    // We check all functions that are in a "lower" scc. These must
    // terminate for all inputs in any case.
    val sccLowerCallees = sccCallees - sccIndex
    val lowerDefs = sccLowerCallees.flatMap(sccArray(_))
    val lowerOK = lowerDefs.forall(terminates(_).isGuaranteed)
    if (!lowerOK)
      return NoGuarantee

    // Now all we need to do is check the functions in the same
    // scc. But who knows, maybe none of these are called?
    if (!sccCallees(sccIndex)) {
      // (the distinction isn't exactly useful...)
      if (sccCallees.isEmpty)
        return Terminates("no calls")
      else
        return Terminates("by subcalls")
    }

    // So now we know the function is recursive (or mutually
    // recursive). Maybe it's just self-recursive?
    if (sccArray(sccIndex).size == 1) {
      assert(sccArray(sccIndex) == Set(funDef))
      // Yes it is !
      // Now we apply a simple recipe: we check that in each (self)
      // call, at least one argument is of an ADT type and decreases.
      // Yes, it's that restrictive.
      val callsOfInterest = { (e: Expr) =>
        functionCallsOf(simplifyLets(matchToIfThenElse(e))).filter(_.tfd.fd == funDef)
      } 

      val callsToAnalyze = callsOfInterest(funDef.fullBody)

      val funDefArgsIDs = funDef.params.map(_.id).toSet

      if (callsToAnalyze.forall { fi =>
        fi.args.exists { arg =>
          isSubTreeOfArg(arg, funDefArgsIDs)
        }
      }) {
        return Terminates("decreasing")
      } else {
        return NoGuarantee
      }
    }

    // Handling mutually recursive functions is beyond my willpower.
    NoGuarantee
  }

  private def isSubTreeOfArg(expr: Expr, args: Set[Identifier]): Boolean = {
    @tailrec
    def rec(e: Expr, fst: Boolean): Boolean = e match {
      case Variable(id) if args(id) => !fst
      case CaseClassSelector(_, cc, _) => rec(cc, false)
      case _ => false
    }
    rec(expr, true)
  }
}
