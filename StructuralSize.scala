/* Copyright 2009-2016 EPFL, Lausanne */

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
  
  /* Absolute value for BigInt type
   *
   * def absBigInt(x: BigInt): BigInt = if (x >= 0) x else -x
   */
  val typedAbsBigIntFun: TypedFunDef = {
    val x = FreshIdentifier("x", IntegerType, alwaysShowUniqueID = true)
    val absFun = new FunDef(FreshIdentifier("absBigInt", alwaysShowUniqueID = true), Seq(), Seq(ValDef(x)), IntegerType)
    absFun.body = Some(IfExpr(
      GreaterEquals(Variable(x), InfiniteIntegerLiteral(0)),
      Variable(x),
      UMinus(Variable(x))
    ))
    absFun.typed
  }

  /* Absolute value for Int (32 bit) type
   *
   * We use a recursive function here as the bv2int functionality provided
   * through SMT solvers is waaaaay too slow. Recursivity requires the
   * postcondition for verification efforts to succeed.
   *
   * def absInt(x: Int): BigInt = (if (x == 0) {
   *   BigInt(0)
   * } else if (x > 0) {
   *   1 + absInt(x - 1)
   * } else {
   *   1 + absInt(-(x + 1)) // avoids -Integer.MIN_VALUE overflow
   * }) ensuring (_ >= 0)
   */
  def typedAbsIntFun: TypedFunDef = {
    val x = FreshIdentifier("x", Int32Type, alwaysShowUniqueID = true)
    val absFun = new FunDef(FreshIdentifier("absInt", alwaysShowUniqueID = true), Seq(), Seq(ValDef(x)), IntegerType)
    absFun.body = Some(IfExpr(
      Equals(Variable(x), IntLiteral(0)),
      InfiniteIntegerLiteral(0),
      IfExpr(
        GreaterThan(Variable(x), IntLiteral(0)),
        Plus(InfiniteIntegerLiteral(1), FunctionInvocation(absFun.typed, Seq(BVMinus(Variable(x), IntLiteral(1))))),
        Plus(InfiniteIntegerLiteral(1), FunctionInvocation(absFun.typed, Seq(BVUMinus(BVPlus(Variable(x), IntLiteral(1))))))
      )))
    val res = FreshIdentifier("res", IntegerType, alwaysShowUniqueID = true)
    absFun.postcondition = Some(Lambda(Seq(ValDef(res)), GreaterEquals(Variable(res), InfiniteIntegerLiteral(0))))
    absFun.typed
  }

  def size(expr: Expr) : Expr = {
    def funDef(ct: ClassType, cases: ClassType => Seq[MatchCase]): FunDef = {
      // we want to reuse generic size functions for sub-types
      val classDef = ct.root.classDef
      val argumentType = classDef.typed
      val typeParams = classDef.tparams.map(_.tp)

      sizeCache.get(argumentType) match {
        case Some(fd) => fd
        case None =>
          val argument = ValDef(FreshIdentifier("x", argumentType, true))
          val formalTParams = typeParams.map(TypeParameterDef)
          val fd = new FunDef(FreshIdentifier("size", alwaysShowUniqueID = true), formalTParams, Seq(argument), IntegerType)
          sizeCache(argumentType) = fd

          val body = simplifyLets(matchToIfThenElse(matchExpr(argument.toVariable, cases(argumentType))))
          val postId = FreshIdentifier("res", IntegerType)
          val postcondition = Lambda(Seq(ValDef(postId)), GreaterThan(Variable(postId), InfiniteIntegerLiteral(0)))

          fd.body = Some(body)
          fd.postcondition = Some(postcondition)
          fd
      }
    }

    def caseClassType2MatchCase(c: CaseClassType): MatchCase = {
      val arguments = c.fields.map(vd => FreshIdentifier(vd.id.name, vd.getType))
      val argumentPatterns = arguments.map(id => WildcardPattern(Some(id)))
      val sizes = arguments.map(id => size(Variable(id)))
      val result = sizes.foldLeft[Expr](InfiniteIntegerLiteral(1))(Plus)
      purescala.Extractors.SimpleCase(CaseClassPattern(None, c, argumentPatterns), result)
    }

    expr.getType match {
      case (ct: ClassType) =>
        val fd = funDef(ct, {
          case (act: AbstractClassType) => act.knownCCDescendants map caseClassType2MatchCase
          case (cct: CaseClassType) => Seq(caseClassType2MatchCase(cct))
        })
        FunctionInvocation(TypedFunDef(fd, ct.tps), Seq(expr))
      case TupleType(argTypes) => argTypes.zipWithIndex.map({
        case (_, index) => size(tupleSelect(expr, index + 1, true))
      }).foldLeft[Expr](InfiniteIntegerLiteral(0))(Plus)
      case IntegerType =>
        FunctionInvocation(typedAbsBigIntFun, Seq(expr)) 
      case Int32Type =>
        FunctionInvocation(typedAbsIntFun, Seq(expr))
      case _ => InfiniteIntegerLiteral(0)
    }
  }

  def lexicographicDecreasing(s1: Seq[Expr], s2: Seq[Expr], strict: Boolean, sizeOfOneExpr: Expr => Expr): Expr = {
    // Note: The Equal and GreaterThan ASTs work for both BigInt and Bitvector

    val sameSizeExprs = for ((arg1, arg2) <- s1 zip s2) yield Equals(sizeOfOneExpr(arg1), sizeOfOneExpr(arg2))

    val greaterBecauseGreaterAtFirstDifferentPos =
      orJoin(for (firstDifferent <- 0 until scala.math.min(s1.length, s2.length)) yield and(
          andJoin(sameSizeExprs.take(firstDifferent)),
          GreaterThan(sizeOfOneExpr(s1(firstDifferent)), sizeOfOneExpr(s2(firstDifferent)))
      ))

    if (s1.length > s2.length || (s1.length == s2.length && !strict)) {
      or(andJoin(sameSizeExprs), greaterBecauseGreaterAtFirstDifferentPos)
    } else {
      greaterBecauseGreaterAtFirstDifferentPos
    }
  }

  def defs : Set[FunDef] = Set(sizeCache.values.toSeq : _*)
}
