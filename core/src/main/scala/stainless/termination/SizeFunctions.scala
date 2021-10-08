/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

class SizeFunctions(val trees: Trees) {
  import trees._
  import dsl._

  private val functions: ListBuffer[FunDef] = new ListBuffer[FunDef]

  def getFunctions(symbols: Symbols) = synchronized {
    val sortIds = symbols.sorts.values.map { sort =>
      fullSizeFun(sort)(using symbols).id
    }.toSet

    val fullSizeIds = fullCache.values.toSet

    val (fullSize, rest) = functions.partition(fd => fullSizeIds.contains(fd.id))
    val (inSyms, outSyms) = fullSize.partition(fd => sortIds.contains(fd.id))

    inSyms ++ rest
  }

  /* Absolute value for BigInt type
   *
   * def BigIntAbs(x: BigInt): BigInt = if (x >= 0) x else -x
   */
  val integerAbs: FunDef = synchronized {
    val fd = mkFunDef(FreshIdentifier("BigIntAbs"))()(_ =>
      (Seq("x" :: IntegerType()), IntegerType(), {
        case Seq(x) =>
          if_(x >= E(BigInt(0))) {
            x
         } else_ {
            -x
          }
      })
    ).copy(flags = Seq(Synthetic))
    functions += fd
    fd
  }

  /* Negative absolute value for bitvector types
   *
   * To avoid -Integer.MIN_VALUE overflow, we use negative absolute value
   * for bitvector integers.
   *
   * def bvAbs(x: BV): BV = if (x >= 0) -x else x
   */

  private val bvCache: MutableMap[BVType, FunDef] = MutableMap.empty

  def bvAbs(tpe: BVType)(using Symbols): FunDef = synchronized {
    val zero = BVLiteral(tpe.signed, 0, tpe.size)
    bvCache.getOrElseUpdate(tpe, {
      val fd = mkFunDef(FreshIdentifier("bvAbs" + tpe.size))()(_ =>
        (Seq("x" :: tpe), tpe, {
          case Seq(x) =>
            if_(x >= zero) {
              -x
            } else_ {
              x
            }
        })
      ).copy(flags = Seq(Synthetic))
      functions += fd
      fd
    })
  }

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

  def bvAbs2Integer(tpe: BVType)(using Symbols): FunDef = {
    if (tpe.signed) signedBVAbs2Integer(tpe) else unsignedBVAbs2Integer(tpe)
  }

  def unsignedBVAbs2Integer(tpe: BVType)(using Symbols): FunDef = synchronized {
    require(!tpe.signed)

    bv2IntegerCache.getOrElseUpdate(tpe, {
        val funID = FreshIdentifier(s"${tpe}AbsToBigInt")
        val zero = BVLiteral(false, 0, tpe.size)
        val one = BVLiteral(false, 1, tpe.size)
        val fd = mkFunDef(funID)()(_ =>
          (Seq("x" :: tpe), IntegerType(), {
            case Seq(x) =>
              Ensuring(
                if_(x === zero) {
                  E(BigInt(0))
                } else_ {
                  E(BigInt(1)) + E(funID)(x - one)
                },
                \("res" :: IntegerType())(res => res >= E(BigInt(0)))
              )
          })
        ).copy(flags = Seq(Synthetic))
        functions += fd
        fd
      }
    )
  }

  def signedBVAbs2Integer(tpe: BVType)(using Symbols): FunDef = synchronized {
    require(tpe.signed)

    bv2IntegerCache.getOrElseUpdate(tpe, {
        val funID = FreshIdentifier(s"${tpe}AbsToBigInt")
        val zero = BVLiteral(true, 0, tpe.size)
        val one = BVLiteral(true, 1, tpe.size)
        val fd = mkFunDef(funID)()(_ =>
          (Seq("x" :: tpe), IntegerType(), {
            case Seq(x) =>
              Ensuring(
                if_(x === zero) {
                  E(BigInt(0))
                } else_ {
                  if_(x > zero) {
                    E(BigInt(1)) + E(funID)(x - one)
                  } else_ {
                    E(BigInt(1)) + E(funID)(-(x + one))
                  }
                },
                \("res" :: IntegerType())(res => res >= E(BigInt(0)))
              )
          })
        ).copy(flags = Seq(Synthetic))
        functions += fd
        fd
      }
    )
  }

  private val fullCache: MutableMap[ADTSort, Identifier] = MutableMap.empty

  def fullSizeId(sort: ADTSort): Identifier = synchronized {
    fullCache.getOrElseUpdate(sort, FreshIdentifier(s"${sort.id.name}PrimitiveSize"))
  }

  private def fullSizeFun(sort: ADTSort)(using Symbols): FunDef = synchronized {
    val id = fullSizeId(sort)
    val tparams = sort.tparams.map(_.tp)

    val tpe = ADTType(sort.id, sort.typeArgs)
    val v = Variable.fresh("x", tpe)
    val fd = new FunDef(
      id,
      sort.tparams,
      Seq(v.toVal),
      IntegerType(),
      Ensuring(MatchExpr(v, sort.typed(tparams).constructors.map { cons =>
        val arguments = cons.fields.map(_.freshen).toList
        val argumentPatterns = arguments.map(vd => WildcardPattern(Some(vd)))
        val base: Expr = if (cons.fields.nonEmpty) IntegerLiteral(1) else IntegerLiteral(0)
        val rhs = arguments.map(vd => fullSize(vd.toVariable)).foldLeft(base)(_ + _)
        MatchCase(ADTPattern(None, cons.id, cons.tps, argumentPatterns), None, rhs)
      }.toList), \("res" :: IntegerType())(res => res >= E(BigInt(0)))).copiedFrom(sort),
      Seq(Synthetic)
    )

    functions += fd

    fd
  }

  /* Fully recursive size computation
   *
   * Computes (positive) size of Stainless types by summing up all sub-elements
   * accessible in the type definition.
   */
  def fullSize(expr: Expr)(using symbols: Symbols): Expr = synchronized {
    expr.getType match {
      case adt: ADTType =>
        val id = fullSizeId(adt.getSort.definition)
        FunctionInvocation(id, adt.tps, Seq(expr))

      case TupleType(argTypes) =>
        argTypes.zipWithIndex
          .map { case (_, index) =>
            fullSize(symbols.tupleSelect(expr, index + 1, true))
          }
          .foldLeft[Expr](IntegerLiteral(0))(_ + _)

      case IntegerType() =>
        FunctionInvocation(integerAbs.id, Seq(), Seq(expr))

      case bv @ BVType(_, _) =>
        FunctionInvocation(bvAbs2Integer(bv).id, Seq(), Seq(expr))

      case _ =>
        IntegerLiteral(0)
    }
  }
}
