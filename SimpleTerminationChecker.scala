/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package termination

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

import scala.collection.mutable.{Map=>MutableMap}

import scala.annotation.tailrec

class SimpleTerminationChecker(context : LeonContext, program : Program) extends TerminationChecker(context, program) {

  val name = "T1"
  val description = "The simplest form of Terminator™"

  private lazy val callGraph : Map[FunDef,Set[FunDef]] =
    program.callGraph.groupBy(_._1).mapValues(_.map(_._2)) // one liner from hell

  private lazy val sccTriple = SCC.scc(callGraph)
  private lazy val sccArray : Array[Set[FunDef]] = sccTriple._1
  private lazy val funDefToSCCIndex : Map[FunDef,Int] = sccTriple._2
  private lazy val sccGraph : Map[Int,Set[Int]] = sccTriple._3

  private def callees(funDef : FunDef) : Set[FunDef] = callGraph.getOrElse(funDef, Set.empty)

  private val answerCache = MutableMap.empty[FunDef,TerminationGuarantee]

  def terminates(funDef : FunDef) = answerCache.getOrElse(funDef, {
    val g = forceCheckTermination(funDef)
    answerCache(funDef) = g
    g
  })

  private def forceCheckTermination(funDef : FunDef) : TerminationGuarantee = {
    // We would have to clarify what it means to terminate.
    // We would probably need something along the lines of:
    //   "Terminates for all values satisfying prec."
    if(funDef.hasPrecondition)
      return NoGuarantee

    // This is also too confusing for me to think about now.
    if(!funDef.hasImplementation)
      return NoGuarantee

    val sccIndex   = funDefToSCCIndex.getOrElse(funDef, {
      return NoGuarantee
    })
    val sccCallees = sccGraph(sccIndex)

    // We check all functions that are in a "lower" scc. These must
    // terminate for all inputs in any case.
    val sccLowerCallees = sccCallees.filterNot(_ == sccIndex)
    val lowerDefs = sccLowerCallees.map(sccArray(_)).foldLeft(Set.empty[FunDef])(_ ++ _)
    val lowerOK = lowerDefs.forall(terminates(_).isGuaranteed)
    if(!lowerOK)
      return NoGuarantee

    // Now all we need to do is check the functions in the same
    // scc. But who knows, maybe none of these are called?
    if(!sccCallees(sccIndex)) {
      // (the distinction isn't exactly useful...)
      if(sccCallees.isEmpty)
        return TerminatesForAllInputs("no calls")
      else
        return TerminatesForAllInputs("by subcalls")
    }

    // So now we know the function is recursive (or mutually
    // recursive). Maybe it's just self-recursive?
    if(sccArray(sccIndex).size == 1) {
      assert(sccArray(sccIndex) == Set(funDef))
      // Yes it is !
      // Now we apply a simple recipe: we check that in each (self)
      // call, at least one argument is of an ADT type and decreases.
      // Yes, it's that restrictive.
      val callsOfInterest = { (oe : Option[Expr]) => 
        oe.map { e =>
          functionCallsOf(
            simplifyLets(
              matchToIfThenElse(e)
            )
          ).filter(_.funDef == funDef)
        } getOrElse Set.empty[FunctionInvocation]
      }

      val callsToAnalyze = callsOfInterest(funDef.body) ++ callsOfInterest(funDef.precondition) ++ callsOfInterest(funDef.postcondition.map(_._2))

      assert(!callsToAnalyze.isEmpty)

      val funDefArgsIDs = funDef.args.map(_.id).toSet

      if(callsToAnalyze.forall { fi =>
        fi.args.exists { arg =>
          isSubTreeOfArg(arg, funDefArgsIDs)
        }
      }) {
        return TerminatesForAllInputs("decreasing")
      } else {
        return NoGuarantee
      }
    }

    // Handling mutually recursive functions is beyond my willpower.
    NoGuarantee 
  }

  private def isSubTreeOfArg(expr : Expr, args : Set[Identifier]) : Boolean = {
    @tailrec
    def rec(e : Expr, fst : Boolean) : Boolean = e match {
      case Variable(id) if(args(id)) => !fst
      case CaseClassSelector(_, cc, _) => rec(cc, false)
      case _ => false
    }
    rec(expr, true)
  }
}
