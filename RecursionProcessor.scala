package leon
package termination

import purescala.Trees._
import purescala.Common._
import purescala.Definitions._

import scala.annotation.tailrec

class RecursionProcessor(checker: TerminationChecker, relationBuilder: RelationBuilder) extends Processor(checker) {

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

  def run(problem: Problem) = if (problem.funDefs.size > 1) (Nil, List(problem)) else {
    val funDef = problem.funDefs.head
    val relations = relationBuilder.run(funDef)
    val (recursive, others) = relations.partition({ case Relation(_, _, FunctionInvocation(fd, _)) => fd == funDef })

    if (others.exists({ case Relation(_, _, FunctionInvocation(tfd, _)) => !checker.terminates(tfd.fd).isGuaranteed })) (Nil, List(problem)) else {
      val decreases = funDef.args.zipWithIndex.exists({ case (arg, index) =>
        recursive.forall({ case Relation(_, _, FunctionInvocation(_, args)) =>
          isSubtreeOf(args(index), arg.id)
        })
      })

      if (!decreases) (Nil, List(problem))
      else (Cleared(funDef) :: Nil, Nil)
    }
  }
}

// vim: set ts=4 sw=4 et:
