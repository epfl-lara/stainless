/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import purescala.Common._

import scala.annotation.tailrec

class RecursionProcessor(val checker: TerminationChecker, val rb: RelationBuilder) extends Processor {

  val name: String = "Recursion Processor"

  private def isSubtreeOf(expr: Expr, id: Identifier) : Boolean = {
    @tailrec
    def rec(e: Expr, fst: Boolean): Boolean = e match {
      case Variable(aid) if aid == id => !fst
      case CaseClassSelector(_, cc, _) => rec(cc, false)
      case _ => false
    }
    rec(expr, true)
  }

  def run(problem: Problem) = if (problem.funDefs.size > 1) None else {
    val funDef = problem.funDefs.head
    val relations = rb.getRelations(funDef)
    val (recursive, others) = relations.partition({ case Relation(_, _, FunctionInvocation(tfd, _), _) => tfd.fd == funDef })

    if (others.exists({ case Relation(_, _, FunctionInvocation(tfd, _), _) => !checker.terminates(tfd.fd).isGuaranteed })) {
      None
    } else {
      val decreases = funDef.params.zipWithIndex.exists({ case (arg, index) =>
        recursive.forall({ case Relation(_, path, FunctionInvocation(_, args), _) =>
          args(index) match {
            // handle case class deconstruction in match expression!
            case Variable(id) => path.bindings.exists {
              case (vid, ccs) if vid == id => isSubtreeOf(ccs, arg.id)
              case _ => false
            }
            case expr => isSubtreeOf(expr, arg.id)
          }
        })
      })

      if (decreases)
        Some(Cleared(funDef) :: Nil)
      else
        None
    }
  }
}
