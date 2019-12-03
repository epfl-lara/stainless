/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package termination

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

trait SizeFunctions {
  val trees: Trees
  import trees._
  import dsl._

  private val functions: ListBuffer[FunDef] = new ListBuffer[FunDef]

  // TODO: change to do it with types and include bv and bv2
  def getFunctions(smbs: Symbols) = synchronized {
    val fullSizeIds = fullCache.values.toList
    val sortIds = smbs.sorts.values.map(_.id).toList.flatMap { id =>
      fullCache.get(id)
    }
    val (fullSize, rest) = functions.partition(fd => fullSizeIds.contains(fd.id))
    val (inSyms, outSyms) = fullSize.partition(fd => sortIds.contains(fd.id))

    inSyms ++ rest
  }

  /* Absolute value for BigInt type
   *
   * def integerAbs(x: BigInt): BigInt = if (x >= 0) x else -x
   */
  val integerAbs: FunDef = synchronized {
    val fd = mkFunDef(FreshIdentifier("integerAbs"))()(_ =>
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

  def bvAbs(tpe: BVType)(implicit symbols: Symbols): FunDef = synchronized {
    bvCache.getOrElseUpdate(tpe, {
      val fd = mkFunDef(FreshIdentifier("bvAbs" + tpe.size))()(_ =>
        (Seq("x" :: tpe), tpe, {
          case Seq(x) =>
            if_(x >= E(0)) {
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

  def bvAbs2Integer(tpe: BVType)(implicit symbols: Symbols): FunDef = synchronized {
    bv2IntegerCache.getOrElseUpdate(
      tpe, {
        val funID = FreshIdentifier("bvAbs2Integer$" + tpe.size)
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

  private val fullCache: MutableMap[Identifier, Identifier] = MutableMap.empty

  /* Fully recursive size computation
   *
   * Computes (positive) size of leon types by summing up all sub-elements
   * accessible in the type definition.
   */
  def fullSize(expr: Expr)(implicit symbols: Symbols): Expr = synchronized {
    expr.getType match {
      case (adt: ADTType) =>
        val sort = adt.getSort.definition
        val tpe = ADTType(sort.id, sort.typeArgs)
        val fid = fullCache.get(sort.id) match {
          case Some(id) => id
          case None =>
            val id = FreshIdentifier(s"${adt.id.name}PrimitiveSize")
            fullCache += sort.id -> id

            // we want to reuse generic size functions for sub-types
            val tparams = sort.tparams.map(_.tp)

            val v = Variable.fresh("x", tpe)

            functions += new FunDef(
              id,
              sort.tparams,
              Seq(v.toVal),
              IntegerType(),
              Ensuring(
                MatchExpr(
                  v,
                  sort.typed(tparams).constructors.map { cons =>
                    val arguments = cons.fields.map(_.freshen)
                    val argumentPatterns = arguments.map(vd => WildcardPattern(Some(vd)))
                    val base: Expr = if (cons.fields.nonEmpty) IntegerLiteral(1) else IntegerLiteral(0)
                    val rhs = arguments.map(vd => fullSize(vd.toVariable)).foldLeft(base)(_ + _)
                    MatchCase(ADTPattern(None, cons.id, cons.tps, argumentPatterns), None, rhs)
                  }
                ),
                \("res" :: IntegerType())(res => res >= E(BigInt(0)))
              ).copiedFrom(expr),
              Seq(Synthetic)
            )

            id
        }

        FunctionInvocation(fid, adt.tps, Seq(expr))

      case TupleType(argTypes) =>
        argTypes.zipWithIndex
          .map({
            case (_, index) => fullSize(symbols.tupleSelect(expr, index + 1, true))
          })
          .foldLeft[Expr](IntegerLiteral(0))(_ + _)

      case IntegerType() =>
        FunctionInvocation(integerAbs.id, Seq(), Seq(expr))

      case bv @ BVType(_, _) =>
        FunctionInvocation(bvAbs2Integer(bv).id, Seq(), Seq(expr))

      case _ => IntegerLiteral(0)
    }
  }

}
