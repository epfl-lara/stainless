package stainless.frontends.fast.elaboration.elaborators

import inox.parser.elaboration.SimpleTypes

import scala.util.parsing.input.Position

trait ExprElaborators extends inox.parser.elaboration.elaborators.ExprElaborators {
  self: stainless.frontends.fast.Elaborators =>

  class StainlessExprE extends super.ExprE {

    /** Whole cast structure taken form package stainless.frontends.dotc.CodeExtraction changes to accommodate this pipeline */
    private def injectCasts(ctor: (trees.Expr, trees.Expr) => trees.Expr)
                           (lhs: trees.Expr, lhstpe: SimpleTypes.Type, rhs: trees.Expr, rhstpe: SimpleTypes.Type): trees.Expr = {
      injectCastsImpl(ctor)(lhs, lhstpe, rhs, rhstpe, shift = false)
    }

    private def injectCastsForShift(ctor: (trees.Expr, trees.Expr) => trees.Expr)
                                   (lhs: trees.Expr, lhsTpe: SimpleTypes.Type, rhs: trees.Expr, rhsTpe: SimpleTypes.Type): trees.Expr = {
      injectCastsImpl(ctor)(lhs, lhsTpe, rhs, rhsTpe, shift = true)
    }

    private def injectCastsImpl(ctor: (trees.Expr, trees.Expr) => trees.Expr)
                               (lhs: trees.Expr, ltpe: SimpleTypes.Type, rhs: trees.Expr, rtpe: SimpleTypes.Type, shift: Boolean): trees.Expr = {
      def checkBits(tr: trees.Tree, tpe: SimpleTypes.Type) = tpe match {
        case SimpleTypes.BitVectorType(_, 8 | 16 | 32 | 64) => // Byte, Short, Int or Long are ok
        case SimpleTypes.BitVectorType(_, s) => throw new Exception(s"Unexpected integer of $s bits")
        case _ => // non-bitvector types are ok too
      }

      checkBits(lhs, ltpe)
      checkBits(rhs, rtpe)

      val id = { e: trees.Expr => e }
      val widen32 = { e: trees.Expr => trees.BVWideningCast(e, trees.BVType(true, 32).copiedFrom(e)).copiedFrom(e) }
      val widen64 = { e: trees.Expr => trees.BVWideningCast(e, trees.BVType(true, 64).copiedFrom(e)).copiedFrom(e) }

      val (lctor, rctor) = (ltpe, rtpe) match {
        case (SimpleTypes.BitVectorType(true, 64), SimpleTypes.BitVectorType(true, 64)) => (id, id)
        case (SimpleTypes.BitVectorType(true, 64), SimpleTypes.BitVectorType(true, _)) => (id, widen64)
        case (SimpleTypes.BitVectorType(true, _), SimpleTypes.BitVectorType(true, 64)) if shift => throw new Exception(s"Unsupported shift")
        case (SimpleTypes.BitVectorType(true, _), SimpleTypes.BitVectorType(true, 64)) => (widen64, id)
        case (SimpleTypes.BitVectorType(true, 32), SimpleTypes.BitVectorType(true, 32)) => (id, id)
        case (SimpleTypes.BitVectorType(true, 32), SimpleTypes.BitVectorType(true, _)) => (id, widen32)
        case (SimpleTypes.BitVectorType(true, _), SimpleTypes.BitVectorType(true, 32)) => (widen32, id)
        case (SimpleTypes.BitVectorType(true, _), SimpleTypes.BitVectorType(true, _)) => (widen32, widen32)

        case (SimpleTypes.BitVectorType(_, _), _) | (_, SimpleTypes.BitVectorType(_, _)) =>
          throw new Exception(s"Unexpected combination of types: $ltpe and $rtpe")

        case (_, _) => (id, id)
      }

      ctor(lctor(lhs), rctor(rhs))
    }

    private def injectCast(ctor: trees.Expr => trees.Expr)(expr: trees.Expr, tpe: SimpleTypes.Type): trees.Expr = {
      val id = { expr: trees.Expr => expr }
      val widen32 = { expr: trees.Expr => trees.BVWideningCast(expr, trees.Int32Type().copiedFrom(expr)).copiedFrom(expr) }

      val ector = tpe match {
        case SimpleTypes.BitVectorType(true, 8 | 16) => widen32
        case SimpleTypes.BitVectorType(true, 32 | 64) => id
        case SimpleTypes.BitVectorType(_, s) => throw new Exception(s"Unexpected integer type: $tpe")
        case _ => id
      }

      ctor(ector(expr))
    }


    override def elaborate(template: Exprs.Expr)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = template match {
      case PatternMatchings.MatchExpression(lhs, cases) =>
        for {
          (tpe, eventualLhs) <- ExprE.elaborate(lhs)
          (rhsType, patternType, cases) <- MatchCaseSeqE.elaborate(cases)
          _ <- Constrained(Constraint.equal(tpe, patternType))
        } yield (rhsType, Eventual.withUnifier { implicit unifier =>
          trees.MatchExpr(eventualLhs.get, cases.get)
        })

      case StainlessExprs.Int64Literal(value) =>
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val v = Eventual.withUnifier { unifier =>
          unifier.get(u) match {
            case SimpleTypes.BitVectorType(true, 64) =>
              trees.Int64Literal(value)
            case _ => throw new IllegalStateException("Unifier returned unexpected value.")
          }
        }
        Constrained.pure((u, v)).addConstraint(Constraint.equal(u, SimpleTypes.BitVectorType(signed = true, 64)))
      case StainlessExprs.Int32Literal(value) =>
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val v = Eventual.withUnifier { unifier =>
          unifier.get(u) match {
            case SimpleTypes.BitVectorType(true, 32) =>
              trees.Int32Literal(value)
            case _ => throw new IllegalStateException("Unifier returned unexpected value.")
          }
        }
        Constrained.pure((u, v)).addConstraint(Constraint.equal(u, SimpleTypes.BitVectorType(signed = true, 32)))


      case StainlessExprs.Int16Literal(value) =>
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val v = Eventual.withUnifier { unifier =>
          unifier.get(u) match {
            case SimpleTypes.BitVectorType(true, 16) => trees.Int16Literal(value)
            case _ => throw new IllegalStateException("Unifier returned unexpected value.")
          }
        }
        Constrained.pure((u, v)).addConstraint(Constraint.equal(u, SimpleTypes.BitVectorType(signed = true, 16)))
      case StainlessExprs.Int8Literal(value) =>
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val v = Eventual.withUnifier { unifier =>
          unifier.get(u) match {
            case SimpleTypes.BitVectorType(true, 8) =>
              trees.Int8Literal(value)
            case _ => throw new IllegalStateException("Unifier returned unexpected value.")
          }
        }
        Constrained.pure((u, v)).addConstraint(Constraint.equal(u, SimpleTypes.BitVectorType(signed = true, 8)))
      // testing overloading addition
      case Exprs.BinaryOperation(Exprs.Binary.Plus, lhs, rhs) => {
        val oneOfUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val resultType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val rhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val lhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val tupleFirst = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val tupleSecond = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val numericType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((resultType, Eventual.withUnifier { implicit unifier =>
              (unifier(lhsTpe), unifier(rhsTpe)) match {
                case (SimpleTypes.StringType(), SimpleTypes.StringType()) =>
                  trees.StringConcat(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.SetType(tpe), elemType) if tpe == elemType =>
                  trees.SetAdd(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.BagType(tpe), elemType) if tpe == elemType =>
                  trees.BagAdd(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.MapType(from, to), SimpleTypes.TupleType(types)) if types.size == 2 && types.head == from && types(1) == to =>
                  val tupleTree = rhsEventual.get
                  trees.MapUpdated(lhsEventual.get, trees.TupleSelect(tupleTree, 1), trees.TupleSelect(tupleTree, 2))
                case (SimpleTypes.IntegerType(), SimpleTypes.IntegerType()) =>
                  trees.Plus(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.BitVectorType(signed1, size1), SimpleTypes.BitVectorType(signed2, size2))
                  if signed1 == signed2 && size1 == size2 =>
                  trees.Plus(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.RealType(), SimpleTypes.RealType()) =>
                  trees.Plus(lhsEventual.get, rhsEventual.get)
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(oneOfUnknown, SimpleTypes.FunctionType(Seq(lhsUnknown, rhsUnknown), resultType),
                  Seq(
                    SimpleTypes.FunctionType(Seq(numericType, numericType), numericType),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.StringType(), SimpleTypes.StringType()), SimpleTypes.StringType()),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(rhsUnknown), rhsUnknown), SimpleTypes.SetType(rhsUnknown)),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(rhsUnknown), rhsUnknown), SimpleTypes.BagType(rhsUnknown)),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.MapType(tupleFirst, tupleSecond), rhsUnknown), SimpleTypes.MapType(tupleFirst, tupleSecond))
                  )))
              .addConstraint(Constraint.oneOf(rhsUnknown, rhsTpe,
                Seq(
                  rhsUnknown,
                  SimpleTypes.TupleType(Seq(tupleFirst, tupleSecond)
                  ))))
              .addConstraint(Constraint.isNumeric(numericType))
              .addConstraint(Constraint.equal(lhsTpe, lhsUnknown))
              .addConstraint(Constraint.equal(lhsTpe, resultType))
              .addConstraint(Constraint.exist(resultType))
              .addConstraint(Constraint.exist(rhsUnknown))
          }
        }
      }

      case Exprs.BinaryOperation(Exprs.Binary.BVAnd, lhs, rhs) =>
        val oneOfUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val resultType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val rhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val lhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val bitsType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((resultType, Eventual.withUnifier { implicit unifier =>
              (unifier(lhsTpe), unifier(rhsTpe)) match {
                case (SimpleTypes.BitVectorType(signed1, size1), SimpleTypes.BitVectorType(signed2, size2)) if signed1 == signed2 && size1 == size2 =>
                  trees.BVAnd(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.SetType(tpe), elemType) if tpe == elemType =>
                  trees.SetIntersection(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.BagType(tpe), elemType) if tpe == elemType =>
                  trees.BagIntersection(lhsEventual.get, rhsEventual.get)
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(oneOfUnknown, SimpleTypes.FunctionType(Seq(lhsUnknown, rhsUnknown), resultType),
                  Seq(
                    SimpleTypes.FunctionType(Seq(bitsType, bitsType), bitsType),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(rhsUnknown), rhsUnknown), SimpleTypes.SetType(rhsUnknown)),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(rhsUnknown), rhsUnknown), SimpleTypes.BagType(rhsUnknown))
                  )))
              .addConstraint(Constraint.isBits(bitsType))
              .addConstraint(Constraint.equal(lhsTpe, lhsUnknown))
              .addConstraint(Constraint.equal(lhsTpe, resultType))
              .addConstraint(Constraint.exist(resultType))
              .addConstraint(Constraint.exist(oneOfUnknown))
          }
        }
      case Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Union, lhs, rhs) =>
        val oneOfUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val dataType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val elemType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((dataType, Eventual.withUnifier { implicit unifier =>
              (unifier(lhsTpe), unifier(rhsTpe)) match {
                case (a: SimpleTypes.SetType, b: SimpleTypes.SetType) if a == b =>
                  trees.SetUnion(lhsEventual.get, rhsEventual.get)
                case (a: SimpleTypes.BagType, b: SimpleTypes.BagType) if a == b =>
                  trees.BagUnion(lhsEventual.get, rhsEventual.get)
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(oneOfUnknown, SimpleTypes.FunctionType(Seq(dataType, dataType), dataType), Seq(
                  SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(elemType), SimpleTypes.SetType(elemType)), SimpleTypes.SetType(elemType)),
                  SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(elemType), SimpleTypes.BagType(elemType)), SimpleTypes.BagType(elemType))
                )
                ))
              .addConstraint(Constraint.equal(lhsTpe, dataType))
              .addConstraint(Constraint.equal(rhsTpe, dataType))
              .addConstraint(Constraint.exist(dataType))
              .addConstraint(Constraint.exist(elemType))
          }
        }
      case Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Difference, lhs, rhs) =>
        val oneOfUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val dataType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val elemType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((dataType, Eventual.withUnifier { implicit unifier =>
              (unifier(lhsTpe), unifier(rhsTpe)) match {
                case (a: SimpleTypes.SetType, b: SimpleTypes.SetType) if a == b =>
                  trees.SetDifference(lhsEventual.get, rhsEventual.get)
                case (a: SimpleTypes.BagType, b: SimpleTypes.BagType) if a == b =>
                  trees.BagDifference(lhsEventual.get, rhsEventual.get)
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(oneOfUnknown, SimpleTypes.FunctionType(Seq(dataType, dataType), dataType), Seq(
                  SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(elemType), SimpleTypes.SetType(elemType)), SimpleTypes.SetType(elemType)),
                  SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(elemType), SimpleTypes.BagType(elemType)), SimpleTypes.BagType(elemType))
                )
                ))
              .addConstraint(Constraint.equal(lhsTpe, dataType))
              .addConstraint(Constraint.equal(rhsTpe, dataType))
              .addConstraint(Constraint.exist(dataType))
              .addConstraint(Constraint.exist(elemType))
              .addConstraint(Constraint.exist(oneOfUnknown))
          }
        }
      case Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Contains, lhs, rhs) =>
        val oneOfUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val dataType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val elemType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((SimpleTypes.BooleanType(), Eventual.withUnifier { implicit unifier =>
              (unifier(lhsTpe), unifier(rhsTpe)) match {
                case (SimpleTypes.SetType(a), b) if a == b =>
                  trees.ElementOfSet(rhsEventual.get, lhsEventual.get)
                case (SimpleTypes.BagType(a), b) if a == b =>
                  trees.MultiplicityInBag(rhsEventual.get, lhsEventual.get)
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(oneOfUnknown, SimpleTypes.FunctionType(Seq(dataType, elemType), SimpleTypes.BooleanType()), Seq(
                  SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(elemType), elemType), SimpleTypes.BooleanType()),
                  SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(elemType), elemType), SimpleTypes.BooleanType())
                )))
              .addConstraint(Constraint.equal(lhsTpe, dataType))
              .addConstraint(Constraint.equal(rhsTpe, elemType))
              .addConstraint(Constraint.exist(dataType))
              .addConstraint(Constraint.exist(elemType))
              .addConstraint(Constraint.exist(oneOfUnknown))
          }
        }

      case Exprs.BinaryOperation(StainlessExprs.AdditionalOperators.Updated, lhs, rhs) =>
        val oneOfUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val resultType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val rhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val lhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val tupleFirst = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val tupleSecond = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((resultType, Eventual.withUnifier { implicit unifier =>
              (unifier(lhsTpe), unifier(rhsTpe)) match {
                case (SimpleTypes.MapType(from, to), SimpleTypes.TupleType(types)) if types.size == 2 && types.head == from && types(1) == to =>
                  val tupleTree = rhsEventual.get
                  trees.MapUpdated(lhsEventual.get, trees.TupleSelect(tupleTree, 1), trees.TupleSelect(tupleTree, 2))
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(oneOfUnknown, SimpleTypes.FunctionType(Seq(lhsUnknown, rhsUnknown), resultType),
                  Seq(
                    SimpleTypes.FunctionType(Seq(SimpleTypes.MapType(tupleFirst, tupleSecond), rhsUnknown), SimpleTypes.MapType(tupleFirst, tupleSecond))
                  )))
              .addConstraint(Constraint.oneOf(oneOfUnknown, rhsTpe,
                Seq(
                  rhsUnknown,
                  SimpleTypes.TupleType(Seq(tupleFirst, tupleSecond)
                  ))))
              .addConstraint(Constraint.equal(lhsTpe, lhsUnknown))
              .addConstraint(Constraint.equal(lhsTpe, resultType))
              .addConstraint(Constraint.exist(resultType))
              .addConstraint(Constraint.exist(oneOfUnknown))
          }
        }

      case StainlessExprs.Require(contract, body) =>
        ExprE.elaborate(contract).flatMap {
          case (contractTpe, contractBody) =>
            ExprE.elaborate(body).flatMap {
              case (bodyType, bodyEventual) => Constrained.pure((
                bodyType, Eventual.withUnifier { implicit unifier =>
                trees.Require(contractBody.get, bodyEventual.get)
              })).addConstraint(Constraint.equal(contractTpe, SimpleTypes.BooleanType()))
            }
        }

      case StainlessExprs.Holds(expr) =>
        ExprE.elaborate(expr).flatMap {
          case (tpe, exp) =>
            Constrained.pure((tpe, Eventual.withUnifier { implicit unifier =>
              val vd = trees.ValDef.fresh("holds", trees.BooleanType())
              val post = trees.Lambda(Seq(vd), vd.toVariable)
              trees.Ensuring(exp.get, post)
            })).addConstraint(Constraint.equal(tpe, SimpleTypes.BooleanType()))
        }
      case StainlessExprs.Ensuring(body, proof) =>
        ExprE.elaborate(body).flatMap {
          case (tpe, exp) =>
            ExprE.elaborate(proof).flatMap {
              case (postTpe, post) =>
                Constrained.pure(tpe, Eventual.withUnifier { implicit unifier =>
                  trees.Ensuring(exp.get, post.get match {
                  case l: trees.Lambda => l.copy(body = l.body).copiedFrom(l)
                  case other =>
                    val vd = trees.ValDef.fresh("res", SimpleTypes.toInox(unifier(tpe)))
                    trees.Lambda(Seq(vd), unifier(tpe) match {
                      case SimpleTypes.BooleanType() => post.get
                      case _ => trees.Application(other, Seq(vd.toVariable))
                    })
                })
              }).addConstraint(Constraint.equal(tpe, SimpleTypes.BooleanType()))
            }
        }
      case _ => super.elaborate(template)
    }
  }

  override val ExprE = new StainlessExprE

  class StainlessExprSeqE extends ExprSeqE {
    override val elaborator = ExprE
  }

  override val ExprSeqE = new StainlessExprSeqE

  class OptExprE extends Elaborator[Either[Position, Exprs.Expr], (SimpleTypes.Type, Eventual[trees.Expr])] {
    override def elaborate(optExpr: Either[Position, Exprs.Expr])(implicit store: Store):
    Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = optExpr match {
      case Right(expr) =>
        ExprE.elaborate(expr)
      case Left(pos) => {
        Constrained.pure((SimpleTypes.BooleanType().setPos(pos), Eventual.pure(trees.BooleanLiteral(true))))
      }
    }
  }

  val OptExprE = new OptExprE
}
