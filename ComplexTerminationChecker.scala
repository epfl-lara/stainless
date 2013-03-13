package leon
package termination

import purescala.Definitions._
import purescala.Trees._

class ComplexTerminationChecker(context: LeonContext, program: Program) extends TerminationChecker(context, program) {
  import scala.collection.mutable.{Map => MutableMap}

  val name = "Complex Termination Checker"
  val description = "A modular termination checker with a few basic modules™"

  private val pipeline = new ProcessingPipeline(
    program, context, // required for solvers and reporting
    new ComponentProcessor(this),
    new RecursionProcessor(this),
    new RelationProcessor(this),
    new ChainProcessor(this),
    new LoopProcessor(this)
  )

  private val clearedMap     : MutableMap[FunDef, String]               = MutableMap()
  private val brokenMap      : MutableMap[FunDef, (String, Seq[Expr])]  = MutableMap()
  def initialize() {
    for ((reason, results) <- pipeline.run; result <- results) result match {
      case Cleared(fd) => clearedMap(fd) = reason
      case Broken(fd, args) => brokenMap(fd) = (reason, args)
    }
  }

  private val terminationMap : MutableMap[FunDef, TerminationGuarantee] = MutableMap()
  def terminates(funDef: FunDef): TerminationGuarantee = terminationMap.get(funDef) match {
    case Some(guarantee) => guarantee
    case None => {
      val guarantee = brokenMap.get(funDef) match {
        case Some((reason, args)) => LoopsGivenInputs(reason, args)
        case None => program.transitiveCallees(funDef) intersect brokenMap.keys.toSet match {
          case set if set.nonEmpty => CallsNonTerminating(set)
          case _ => if (pipeline.clear(funDef)) clearedMap.get(funDef) match {
            case Some(reason) => Terminates(reason)
            case None => scala.sys.error(funDef.id + " -> not problem, but not cleared or broken ??")
          } else NoGuarantee
        }
      }

      if (guarantee != NoGuarantee) {
        terminationMap(funDef) = guarantee
      }

      guarantee
    }
  }
}
