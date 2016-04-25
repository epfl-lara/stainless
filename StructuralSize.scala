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

  /* Negative absolute value for Int type
   *
   * To avoid -Integer.MIN_VALUE overflow, we use negative absolute value
   * for bitvector integers.
   *
   * def absInt(x: Int): Int = if (x >= 0) -x else x
   */
  val typedAbsIntFun: TypedFunDef = {
    val x = FreshIdentifier("x", Int32Type, alwaysShowUniqueID = true)
    val absFun = new FunDef(FreshIdentifier("absInt", alwaysShowUniqueID = true), Seq(), Seq(ValDef(x)), Int32Type)
    absFun.body = Some(IfExpr(
      GreaterEquals(Variable(x), IntLiteral(0)),
      BVUMinus(Variable(x)),
      Variable(x)
    ))
    absFun.typed
  }

  /* Absolute value for Int (32 bit) type into mathematical integers
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
  def typedAbsInt2IntegerFun: TypedFunDef = {
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

  private val fullCache: MutableMap[TypeTree, FunDef] = MutableMap.empty

  /* Fully recursive size computation
   *
   * Computes (positive) size of leon types by summing up all sub-elements
   * accessible in the type definition.
   */
  def fullSize(expr: Expr) : Expr = {
    def funDef(ct: ClassType, cases: ClassType => Seq[MatchCase]): FunDef = {
      // we want to reuse generic size functions for sub-types
      val classDef = ct.root.classDef
      val argumentType = classDef.typed
      val typeParams = classDef.tparams.map(_.tp)

      fullCache.get(argumentType) match {
        case Some(fd) => fd
        case None =>
          val argument = ValDef(FreshIdentifier("x", argumentType, true))
          val formalTParams = typeParams.map(TypeParameterDef)
          val fd = new FunDef(FreshIdentifier("fullSize", alwaysShowUniqueID = true), formalTParams, Seq(argument), IntegerType)
          fullCache(argumentType) = fd

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
      val sizes = arguments.map(id => fullSize(Variable(id)))
      val result = sizes.foldLeft[Expr](InfiniteIntegerLiteral(1))(Plus)
      purescala.Extractors.SimpleCase(CaseClassPattern(None, c, argumentPatterns), result)
    }

    expr.getType match {
      case (ct: ClassType) =>
        val fd = funDef(ct.root, {
          case (act: AbstractClassType) => act.knownCCDescendants map caseClassType2MatchCase
          case (cct: CaseClassType) => Seq(caseClassType2MatchCase(cct))
        })
        FunctionInvocation(TypedFunDef(fd, ct.tps), Seq(expr))
      case TupleType(argTypes) => argTypes.zipWithIndex.map({
        case (_, index) => fullSize(tupleSelect(expr, index + 1, true))
      }).foldLeft[Expr](InfiniteIntegerLiteral(0))(plus)
      case IntegerType =>
        FunctionInvocation(typedAbsBigIntFun, Seq(expr))
      case Int32Type =>
        FunctionInvocation(typedAbsInt2IntegerFun, Seq(expr))
      case _ => InfiniteIntegerLiteral(0)
    }
  }

  private val outerCache: MutableMap[TypeTree, FunDef] = MutableMap.empty

  object ContainerType {
    def unapply(c: ClassType): Option[(CaseClassType, Seq[(Identifier, TypeTree)])] = c match {
      case cct @ CaseClassType(ccd, _) =>
        if (cct.fields.exists(arg => purescala.TypeOps.isSubtypeOf(arg.getType, cct.root))) None
        else if (ccd.hasParent && ccd.parent.get.knownDescendants.size > 1) None
        else Some((cct, cct.fields.map(arg => arg.id -> arg.getType)))
      case _ => None
    }
  }

  def flatTypesPowerset(tpe: TypeTree): Set[Expr => Expr] = {
    def powerSetToFunSet(l: TraversableOnce[Expr => Expr]): Set[Expr => Expr] = {
      l.toSet.subsets.filter(_.nonEmpty).map{
        (reconss : Set[Expr => Expr]) => (e : Expr) => 
          tupleWrap(reconss.toSeq map { f => f(e) })
      }.toSet
    }

    def rec(tpe: TypeTree): Set[Expr => Expr] = tpe match  {
      case ContainerType(cct, fields) =>
        powerSetToFunSet(fields.zipWithIndex.flatMap { case ((fieldId, fieldTpe), index) =>
          rec(fieldTpe).map(recons => (e: Expr) => recons(caseClassSelector(cct, e, fieldId)))
        })
      case TupleType(tpes) =>
        powerSetToFunSet(tpes.indices.flatMap { case index =>
          rec(tpes(index)).map(recons => (e: Expr) => recons(tupleSelect(e, index + 1, true)))
        })
      case _ => Set((e: Expr) => e)
    }

    rec(tpe)
  }

  def flatType(tpe: TypeTree): Set[Expr => Expr] = {
    def rec(tpe: TypeTree): Set[Expr => Expr] = tpe match {
      case ContainerType(cct, fields) =>
        fields.zipWithIndex.flatMap { case ((fieldId, fieldTpe), index) =>
          rec(fieldTpe).map(recons => (e: Expr) => recons(caseClassSelector(cct, e, fieldId)))
        }.toSet
      case TupleType(tpes) =>
        tpes.indices.flatMap { case index =>
          rec(tpes(index)).map(recons => (e: Expr) => recons(tupleSelect(e, index + 1, true)))
        }.toSet
      case _ => Set((e: Expr) => e)
    }

    rec(tpe)
  }

  /* Recursively computes outer datastructure size
   *
   * Computes the structural size of a datastructure but only considers
   * the outer-most datatype definition.
   *
   * eg. for List[List[T]], the inner list size is not considered
   */
  def outerSize(expr: Expr) : Expr = {
    def dependencies(ct: ClassType): Set[ClassType] = {
      def deps(ct: ClassType): Set[ClassType] = ct.fieldsTypes.collect { case ct: ClassType => ct.root }.toSet
      utils.fixpoint((cts: Set[ClassType]) => cts ++ cts.flatMap(deps))(Set(ct))
    }

    flatType(expr.getType).foldLeft[Expr](InfiniteIntegerLiteral(0)) { case (i, f) =>
      val e = f(expr)
      plus(i, e.getType match {
        case ct: ClassType =>
          val root = ct.root
          val fd = outerCache.getOrElse(root.classDef.typed, {
            val tcd = root.classDef.typed
            val id = FreshIdentifier("x", tcd, true)
            val fd = new FunDef(FreshIdentifier("outerSize", alwaysShowUniqueID = true),
              root.classDef.tparams,
              Seq(ValDef(id)),
              IntegerType)
            outerCache(tcd) = fd

            fd.body = Some(MatchExpr(Variable(id), tcd.knownCCDescendants map { cct =>
              val args = cct.fields.map(_.id.freshen)
              purescala.Extractors.SimpleCase(
                CaseClassPattern(None, cct, args.map(id => WildcardPattern(Some(id)))),
                args.foldLeft[Expr](InfiniteIntegerLiteral(1)) { case (e, id) =>
                  plus(e, id.getType match {
                    case ct: ClassType if dependencies(tcd)(ct.root) => outerSize(Variable(id))
                    case _ => InfiniteIntegerLiteral(0)
                  })
                })
            }))

            val res = FreshIdentifier("res", IntegerType, true)
            fd.postcondition = Some(Lambda(Seq(ValDef(res)), GreaterEquals(Variable(res), InfiniteIntegerLiteral(0))))
            fd
          })

          FunctionInvocation(fd.typed(root.tps), Seq(e))

        case _ => InfiniteIntegerLiteral(0)
      })
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
}
