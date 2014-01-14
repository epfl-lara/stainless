package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

class StructuralSize() {
  import scala.collection.mutable.{Map => MutableMap}

  private val sizeFunctionCache : MutableMap[TypeTree, TypedFunDef] = MutableMap()

  def size(expr: Expr) : Expr = {
    def funDef(tpe: TypeTree, cases: => Seq[MatchCase]) = {
      // we want to reuse generic size functions for sub-types
      val argumentType = tpe match {
        case CaseClassType(cd, tpes) if cd.parent.isDefined => classDefToClassType(cd.parent.get.classDef, tpes)
        case _ => tpe
      }

      sizeFunctionCache.get(argumentType) match {
        case Some(fd) => fd
        case None =>
          val argument = VarDecl(FreshIdentifier("x"), argumentType)
          val fd = new FunDef(FreshIdentifier("size", true), Nil, Int32Type, Seq(argument))
          val tfd = fd.typed(Nil)
          sizeFunctionCache(argumentType) = tfd

          val body = simplifyLets(matchToIfThenElse(MatchExpr(argument.toVariable, cases)))
          val postId = FreshIdentifier("res", false).setType(Int32Type)
          val postSubcalls = functionCallsOf(body).map(GreaterThan(_, IntLiteral(0))).toSeq
          val postRecursive = GreaterThan(Variable(postId), IntLiteral(0))
          val postcondition = And(postSubcalls :+ postRecursive)

          fd.body = Some(body)
          fd.postcondition = Some(postId, postcondition)

          tfd
      }
    }

    def caseClassType2MatchCase(ct: ClassType): MatchCase = ct match {
      case cct: CaseClassType =>
          val arguments = cct.fields.map(f => f -> f.id.freshen)
          val argumentPatterns = arguments.map(p => WildcardPattern(Some(p._2)))
          val sizes = arguments.map(p => size(Variable(p._2)))
          val result = sizes.foldLeft[Expr](IntLiteral(1))(Plus(_,_))
          SimpleCase(CaseClassPattern(None, cct, argumentPatterns), result)
      case _ =>
        sys.error("woot?")
    }

    expr.getType match {
      case a: AbstractClassType =>
        val sizeFd = funDef(a, a.knownCCDescendents.map(caseClassType2MatchCase))
        FunctionInvocation(sizeFd, Seq(expr))
      case c: CaseClassType =>
        val sizeFd = funDef(c, Seq(caseClassType2MatchCase(c)))
        FunctionInvocation(sizeFd, Seq(expr))
      case TupleType(argTypes) => argTypes.zipWithIndex.map({
        case (_, index) => size(TupleSelect(expr, index + 1))
      }).foldLeft[Expr](IntLiteral(0))(Plus(_,_))
      case _ => IntLiteral(0)
    }
  }

  def defs : Set[FunDef] = sizeFunctionCache.values.map(_.fd).toSet
}

// vim: set ts=4 sw=4 et:
