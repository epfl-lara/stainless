/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.Definitions._
import purescala.Constructors._
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
          val argument = ValDef(FreshIdentifier("x", argumentType, true))
          val formalTParams = typeParams.map(TypeParameterDef)
          val fd = new FunDef(FreshIdentifier("size", alwaysShowUniqueID = true), formalTParams, IntegerType, Seq(argument), DefType.MethodDef)
          sizeCache(argumentType) = fd

          val body = simplifyLets(matchToIfThenElse(matchExpr(argument.toVariable, cases(argumentType))))
          val postId = FreshIdentifier("res", IntegerType)
          val postcondition = Lambda(Seq(ValDef(postId)), GreaterThan(Variable(postId), InfiniteIntegerLiteral(0)))

          fd.body = Some(body)
          fd.postcondition = Some(postcondition)
          fd
      }
    }

    def caseClassType2MatchCase(_c: ClassType): MatchCase = {
      val c = _c.asInstanceOf[CaseClassType] // required by leon framework
      val arguments = c.fields.map(vd => FreshIdentifier(vd.id.name, vd.getType))
      val argumentPatterns = arguments.map(id => WildcardPattern(Some(id)))
      val sizes = arguments.map(id => size(Variable(id)))
      val result = sizes.foldLeft[Expr](InfiniteIntegerLiteral(1))(Plus)
      purescala.Extractors.SimpleCase(CaseClassPattern(None, c, argumentPatterns), result)
    }

    expr.getType match {
      case (ct: ClassType) =>
        val fd = funDef(ct, {
          case (act: AbstractClassType) => act.knownCCDescendents map caseClassType2MatchCase
          case (cct: CaseClassType) => Seq(caseClassType2MatchCase(cct))
        })
        FunctionInvocation(TypedFunDef(fd, ct.tps), Seq(expr))
      case TupleType(argTypes) => argTypes.zipWithIndex.map({
        case (_, index) => size(tupleSelect(expr, index + 1, true))
      }).foldLeft[Expr](InfiniteIntegerLiteral(0))(Plus)
      case _ => InfiniteIntegerLiteral(0)
    }
  }

  def defs : Set[FunDef] = Set(sizeCache.values.toSeq : _*)
}

// vim: set ts=4 sw=4 et:
