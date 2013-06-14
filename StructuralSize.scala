package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

case class TypedExpr(expr: Expr, tpe: TypeTree)

object StructuralSize {
  import scala.collection.mutable.{Map => MutableMap}

  implicit def exprToTypedExpr(expr: Expr): TypedExpr = {
    assert(expr.getType != Untyped)
    TypedExpr(expr, expr.getType)
  }

  private val sizeFunctionCache : MutableMap[TypeTree, FunDef] = MutableMap()
  def size(typedExpr: TypedExpr) : Expr = {
    def funDef(tpe: TypeTree, cases: => Seq[MatchCase]) = {
      // we want to reuse generic size functions for sub-types
      val argumentType = tpe match {
        case CaseClassType(cd) if cd.parent.isDefined => classDefToClassType(cd.parent.get)
        case _ => tpe
      }

      sizeFunctionCache.get(argumentType) match {
        case Some(fd) => fd
        case None =>
          val argument = VarDecl(FreshIdentifier("x"), argumentType)
          val fd = new FunDef(FreshIdentifier("size", true), Int32Type, Seq(argument))
          sizeFunctionCache(argumentType) = fd

          val body = simplifyLets(matchToIfThenElse(MatchExpr(argument.toVariable, cases)))
          val postSubcalls = functionCallsOf(body).map(GreaterThan(_, IntLiteral(0))).toSeq
          val postRecursive = GreaterThan(ResultVariable(), IntLiteral(0))
          val postcondition = And(postSubcalls :+ postRecursive)

          fd.body = Some(body)
          fd.postcondition = Some(postcondition)
          fd
      }
    }

    def caseClassType2MatchCase(_c: ClassTypeDef): MatchCase = {
      val c = _c.asInstanceOf[CaseClassDef] // required by leon framework
      val arguments = c.fields.map(f => f -> f.id.freshen)
      val argumentPatterns = arguments.map(p => WildcardPattern(Some(p._2)))
      val sizes = arguments.map(p => size(TypedExpr(Variable(p._2), p._1.tpe)))
      val result = sizes.foldLeft[Expr](IntLiteral(1))(Plus(_,_))
      SimpleCase(CaseClassPattern(None, c, argumentPatterns), result)
    }

    typedExpr match {
      case TypedExpr(expr, a: AbstractClassType) =>
        val sizeFd = funDef(a, a.classDef.knownChildren map caseClassType2MatchCase)
        FunctionInvocation(sizeFd, Seq(expr))
      case TypedExpr(expr, c: CaseClassType) =>
        val sizeFd = funDef(c, Seq(caseClassType2MatchCase(c.classDef)))
        FunctionInvocation(sizeFd, Seq(expr))
      case TypedExpr(expr, TupleType(argTypes)) => argTypes.zipWithIndex.map({
        case (tpe, index) => size(TypedExpr(TupleSelect(expr, index + 1), tpe))
      }).foldLeft[Expr](IntLiteral(0))(Plus(_,_))
      case _ => IntLiteral(0)
    }
  }

  def defs : Set[FunDef] = Set(sizeFunctionCache.values.toSeq : _*)

  def init : Unit = sizeFunctionCache.clear
}

// vim: set ts=4 sw=4 et:
