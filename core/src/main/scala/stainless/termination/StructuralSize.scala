/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

trait StructuralSize { self: SolverProvider =>

  val checker: ProcessingPipeline
  import checker.program.trees._
  import checker.program.symbols._
  import dsl._

  private val functions: ListBuffer[FunDef] = new ListBuffer[FunDef]

  registerTransformer(new inox.transformers.SymbolTransformer {
    val s: trees.type = trees
    val t: trees.type = trees

    def transform(s: Symbols): Symbols = s.withFunctions(functions)
  })

  /* Absolute value for BigInt type
   *
   * def integerAbs(x: BigInt): BigInt = if (x >= 0) x else -x
   */
  val integerAbs: FunDef = mkFunDef(FreshIdentifier("integerAbs"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      if_ (x >= E(BigInt(0))) {
        x
      } else_ {
        -x
      }
    }))
  functions += integerAbs

  private val bvCache: MutableMap[BVType, FunDef] = MutableMap.empty

  /* Negative absolute value for bitvector types
   *
   * To avoid -Integer.MIN_VALUE overflow, we use negative absolute value
   * for bitvector integers.
   *
   * def bvAbs(x: BV): BV = if (x >= 0) -x else x
   */
  def bvAbs(tpe: BVType): FunDef = bvCache.getOrElse(tpe, {
    val fd = mkFunDef(FreshIdentifier("bvAbs" + tpe.size))()(_ => (
      Seq("x" :: tpe), tpe, { case Seq(x) =>
        if_ (x >= E(0)) {
          -x
        } else_ {
          x
        }
      }))
    functions += fd
    clearSolvers()
    bvCache(tpe) = fd
    fd
  })

  private val bv2IntegerCache: MutableMap[BVType, FunDef] = MutableMap.empty

  /* Absolute value for bitvector type into mathematical integers
   *
   * We use a recursive function here as the bv2int functionality provided
   * through SMT solvers is waaaaay too slow. Recursivity requires the
   * postcondition for verification efforts to succeed.
   *
   * def bvAbs2Integer(x: BV): BigInt = (if (x == 0) {
   *   BigInt(0)
   * } else if (x > 0) {
   *   1 + bvAbs2Integer(x - 1)
   * } else {
   *   1 + bvAbs2Integer(-(x + 1)) // avoids -Integer.MIN_VALUE overflow
   * }) ensuring (_ >= 0)
   */
  def bvAbs2Integer(tpe: BVType): FunDef = bv2IntegerCache.getOrElse(tpe, {
    val funID = FreshIdentifier("bvAbs2Integer$" + tpe.size)
    val zero = BVLiteral(true, 0, tpe.size)
    val one = BVLiteral(true, 1, tpe.size)
    val fd = mkFunDef(funID)()(_ => (
      Seq("x" :: tpe), IntegerType(), { case Seq(x) =>
        Ensuring(if_ (x === zero) {
          E(BigInt(0))
        } else_ {
          if_ (x > zero) {
            E(BigInt(1)) + E(funID)(x - one)
          } else_ {
            E(BigInt(1)) + E(funID)(-(x + one))
          }
        }, \("res" :: IntegerType())(res => res >= E(BigInt(0))))
      }))
    functions += fd
    clearSolvers()
    bv2IntegerCache(tpe) = fd
    fd
  })

  private val fullCache: MutableMap[Type, Identifier] = MutableMap.empty

  /* Fully recursive size computation
   *
   * Computes (positive) size of leon types by summing up all sub-elements
   * accessible in the type definition.
   */
  def fullSize(expr: Expr): Expr = expr.getType match {
    case (adt: ADTType) =>
      val sort = adt.getSort.definition
      val tpe = ADTType(sort.id, sort.typeArgs)
      val fid = fullCache.get(tpe) match {
        case Some(id) => id
        case None =>
          val id = FreshIdentifier("fullSize$" + adt.id.name)
          fullCache += tpe -> id

          // we want to reuse generic size functions for sub-types
          val tparams = sort.tparams.map(_.tp)

          val v = Variable.fresh("x", tpe)
          functions += new FunDef(
            id,
            sort.tparams,
            Seq(v.toVal),
            IntegerType(),
            Ensuring(MatchExpr(v, sort.typed(tparams).constructors.map { cons =>
              val arguments = cons.fields.map(_.freshen)
              val argumentPatterns = arguments.map(vd => WildcardPattern(Some(vd)))
              val base: Expr = if (cons.fields.nonEmpty) IntegerLiteral(1) else IntegerLiteral(0)
              val rhs = arguments.map(vd => fullSize(vd.toVariable)).foldLeft(base)(_ + _)
              MatchCase(ADTPattern(None, cons.id, cons.tps, argumentPatterns), None, rhs)
            }), \("res" :: IntegerType())(res => res >= E(BigInt(0)))).copiedFrom(expr),
            Seq.empty
          )
          clearSolvers()

          id
      }

      FunctionInvocation(fid, adt.tps, Seq(expr))

    case TupleType(argTypes) => argTypes.zipWithIndex.map({
      case (_, index) => fullSize(tupleSelect(expr, index + 1, true))
    }).foldLeft[Expr](IntegerLiteral(0))(_ + _)

    case IntegerType() =>
      FunctionInvocation(integerAbs.id, Seq(), Seq(expr))

    case bv @ BVType(_, _) =>
      FunctionInvocation(bvAbs2Integer(bv).id, Seq(), Seq(expr))

    case _ => IntegerLiteral(0)
  }

  // An ADT sort corresponds to a container type if (and only if) it has
  // a single non-recursive constructor
  object ContainerType {
    def unapply(c: ADTType): Option[Seq[ValDef]] = c.getSort.constructors match {
      case Seq(tcons) =>
        if (tcons.fields.exists(vd => isSubtypeOf(vd.tpe, c))) None
        else Some(tcons.fields)
      case _ => None
    }
  }

  def flatTypesPowerset(tpe: Type): Set[Expr => Expr] = {
    def powerSetToFunSet(l: TraversableOnce[Expr => Expr]): Set[Expr => Expr] = {
      l.toSet.subsets.filter(_.nonEmpty).map{
        (reconss: Set[Expr => Expr]) => (e : Expr) =>
          tupleWrap(reconss.toSeq map { f => f(e) })
      }.toSet
    }

    powerSetToFunSet(flatTypes(tpe))
  }

  def flatTypes(tpe: Type): Set[Expr => Expr] = {
    def rec(tpe: Type): Set[Expr => Expr] = tpe match {
      case ContainerType(fields) =>
        fields.flatMap {
          vd => rec(vd.tpe).map(recons => (e: Expr) => recons(adtSelector(e, vd.id)))
        }.toSet
      case TupleType(tpes) =>
        tpes.indices.flatMap {
          index => rec(tpes(index)).map(recons => (e: Expr) => recons(tupleSelect(e, index + 1, true)))
        }.toSet
      case _ => Set((e: Expr) => e)
    }

    rec(tpe)
  }

  def lexicographicallySmaller(s1: Seq[Expr], s2: Seq[Expr], strict: Boolean, sizeOfOneExpr: Expr => Expr): Expr = {
    // Note: The Equal and LessThan ASTs work for both BigInt and Bitvector

    val sameSizeExprs = for ((arg1, arg2) <- s1 zip s2) yield Equals(sizeOfOneExpr(arg1), sizeOfOneExpr(arg2))

    val lessBecauseLessAtFirstDifferentPos =
      orJoin(for (firstDifferent <- 0 until scala.math.min(s1.length, s2.length)) yield and(
          andJoin(sameSizeExprs.take(firstDifferent)),
          LessThan(sizeOfOneExpr(s1(firstDifferent)), sizeOfOneExpr(s2(firstDifferent)))
      ))

    if (s1.length > s2.length || (s1.length == s2.length && !strict)) {
      or(andJoin(sameSizeExprs), lessBecauseLessAtFirstDifferentPos)
    } else {
      lessBecauseLessAtFirstDifferentPos
    }
  }
}
