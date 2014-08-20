/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

import scala.collection.mutable.{Map => MutableMap}

trait StructuralSize {

  private val sizeCache : MutableMap[TypeTree, FunDef] = MutableMap.empty

  def size(expr: Expr) : Expr = {
    def funDef(ct: ClassType, cases: ClassType => Seq[MatchCase]): FunDef = {
      // we want to reuse generic size functions for sub-types
      val (argumentType, typeParams) = ct match {
        case (cct : CaseClassType) if cct.parent.isDefined =>
          val classDef = cct.parent.get.classDef
          val tparams = classDef.tparams.map(_.tp)
          (classDefToClassType(classDef, tparams), tparams)
        case (ct : ClassType) =>
          val tparams = ct.classDef.tparams.map(_.tp)
          (classDefToClassType(ct.classDef, tparams), tparams)
      }

      sizeCache.get(argumentType) match {
        case Some(fd) => fd
        case None =>
          val argument = ValDef(FreshIdentifier("x").setType(argumentType), argumentType)
          val formalTParams = typeParams.map(TypeParameterDef(_))
          val fd = new FunDef(FreshIdentifier("size", true), formalTParams, Int32Type, Seq(argument), DefType.MethodDef)
          sizeCache(argumentType) = fd

          val body = simplifyLets(matchToIfThenElse(MatchExpr(argument.toVariable, cases(argumentType))))
          val postId = FreshIdentifier("res", false).setType(Int32Type)
          val postcondition = GreaterThan(Variable(postId), IntLiteral(0))

          fd.body = Some(body)
          fd.postcondition = Some(postId, postcondition)
          fd
      }
    }

    def caseClassType2MatchCase(_c: ClassType): MatchCase = {
      val c = _c.asInstanceOf[CaseClassType] // required by leon framework
      val arguments = c.fields.map(f => f -> f.id.freshen)
      val argumentPatterns = arguments.map(p => WildcardPattern(Some(p._2)))
      val sizes = arguments.map(p => size(Variable(p._2)))
      val result = sizes.foldLeft[Expr](IntLiteral(1))(Plus(_,_))
      SimpleCase(CaseClassPattern(None, c, argumentPatterns), result)
    }

    expr.getType match {
      case (ct: ClassType) =>
        val fd = funDef(ct, _ match {
          case (act: AbstractClassType) => act.knownCCDescendents map caseClassType2MatchCase
          case (cct: CaseClassType) => Seq(caseClassType2MatchCase(cct))
        })
        FunctionInvocation(TypedFunDef(fd, ct.tps), Seq(expr))
      case TupleType(argTypes) => argTypes.zipWithIndex.map({
        case (_, index) => size(TupleSelect(expr, index + 1))
      }).foldLeft[Expr](IntLiteral(0))(Plus(_,_))
      case _ => IntLiteral(0)
    }
  }

  def defs : Set[FunDef] = Set(sizeCache.values.toSeq : _*)
}

// vim: set ts=4 sw=4 et:
