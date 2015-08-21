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
  
  // function absBigInt(x: BigInt): BigInt = if (x >= 0) x else -x
  val typedAbsBigIntFun = makeAbsFun(IntegerType, "absBigInt", e => UMinus(e), InfiniteIntegerLiteral(0))

  // function absInt(x: Int): Int = if (x >= 0) x else -x
  val typedAbsIntFun = makeAbsFun(Int32Type, "absInt", e => BVUMinus(e), IntLiteral(0))

  def makeAbsFun(tp: TypeTree, name: String, uminus: Expr => Expr, zero: Expr): TypedFunDef = {
    val x = FreshIdentifier("x", tp, alwaysShowUniqueID = true)
    val absFun = new FunDef(
      FreshIdentifier(name, alwaysShowUniqueID = true),
      Seq(), // no type params 
      tp, // return type
      Seq(ValDef(x))
    )
    absFun.body = Some(IfExpr(
      GreaterEquals(Variable(x), zero),
      Variable(x),
      uminus(Variable(x))
    ))
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
          val fd = new FunDef(FreshIdentifier("size", alwaysShowUniqueID = true), formalTParams, IntegerType, Seq(argument))
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
