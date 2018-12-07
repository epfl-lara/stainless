package stainless.frontends.fast.elaboration.elaborators

import scala.util.parsing.input.Position

trait ExprElaborators extends inox.parser.elaboration.elaborators.ExprElaborators { self: stainless.frontends.fast.Elaborators =>

  class StainlessExprE extends super.ExprE {

    override def elaborate(template: Exprs.Expr)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = template match {
      case PatternMatchings.MatchExpression(lhs, cases) =>
        for {
          (tpe, eventualLhs) <- ExprE.elaborate(lhs)
          (rhsType, patternType , cases) <- MatchCaseSeqE.elaborate(cases)
          _ <- Constrained(Constraint.equal(tpe, patternType))
        } yield (rhsType, Eventual.withUnifier {implicit unifier =>
          trees.MatchExpr(eventualLhs.get, cases.get)
        })
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
      case Exprs.BinaryOperation(Exprs.Binary.Plus, lhs, rhs) =>
        val resultType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val rhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val lhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((resultType, Eventual.withUnifier { implicit unifier =>
              (unifier.get(lhsUnknown), unifier.get(rhsUnknown)) match {
                case (SimpleTypes.IntegerType(), SimpleTypes.IntegerType()) =>
                  trees.Plus(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.BitVectorType(signed1, size1), SimpleTypes.BitVectorType(signed2, size2))
                  if signed1 == signed2 && size1 == size2 =>
                  trees.Plus(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.RealType(), SimpleTypes.RealType()) =>
                  trees.Plus(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.StringType(), SimpleTypes.StringType()) =>
                  trees.StringConcat(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.SetType(tpe), elemType) if tpe == elemType =>
                  trees.SetAdd(lhsEventual.get, rhsEventual.get)
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(StainlessConstraint.
                oneOf(lhsTpe, {
                  case a@SimpleTypes.SetType(elem) =>
                    Seq(Constraints.Equals(elem, rhsTpe))
                  case a@SimpleTypes.BagType(elem) =>
                    Seq(Constraints.Equals(elem, rhsTpe))
                  case a@SimpleTypes.MapType(from, to) =>
                    Seq(Constraints.Equals(SimpleTypes.TupleType(Seq(from, to)), rhsTpe))
                  case SimpleTypes.StringType() =>
                    Seq(Constraints.Equals(rhsTpe, SimpleTypes.StringType()))
                  case a =>
                    Seq(Constraints.Equals(rhsTpe, a), Constraint.isNumeric(a))
                }
                ))
              .addConstraint(StainlessConstraint.oneOf(rhsTpe, {
                case SimpleTypes.StringType() => Seq(StainlessConstraint.oneOf(lhsTpe, {
                  case SimpleTypes.StringType() => Seq(
                    Constraint.equal(SimpleTypes.StringType(), rhsTpe), Constraint.equal(resultType, SimpleTypes.StringType()))
                  case SimpleTypes.SetType(elem) => Seq(
                    Constraint.equal(elem, SimpleTypes.StringType()), Constraint.equal(resultType, SimpleTypes.SetType(rhsTpe))
                  )
                  case SimpleTypes.BagType(elem) => Seq(
                    Constraint.equal(elem, SimpleTypes.StringType()), Constraint.equal(resultType, SimpleTypes.BagType(rhsTpe))
                  )
                  case _ => throw new IllegalStateException("Overloading with right hand as string not possible.")
                }))
                case SimpleTypes.BitVectorType(_, _) => Seq(StainlessConstraint.oneOf(lhsTpe, {
                  case ltpe: SimpleTypes.BitVectorType => Seq(Constraint.equal(ltpe, rhsTpe))
                  case SimpleTypes.SetType(elem) =>
                    Seq(Constraint.equal(elem, rhsTpe), Constraint.equal(resultType, SimpleTypes.SetType(rhsTpe)))
                  case SimpleTypes.BagType(elem) =>
                    Seq(Constraint.equal(elem, rhsTpe), Constraint.equal(resultType, SimpleTypes.BagType(rhsTpe)))
                  case _ => throw new IllegalStateException("Overloading with right hand as bit vector.")
                }))
                case SimpleTypes.IntegerType() => Seq(StainlessConstraint.oneOf(lhsTpe, {
                  case SimpleTypes.IntegerType() => Seq(Constraint.equal(SimpleTypes.IntegerType(), lhsTpe))
                  case SimpleTypes.SetType(elem) =>
                    Seq(Constraint.equal(elem, rhsTpe), Constraint.equal(resultType, SimpleTypes.SetType(rhsTpe)))
                  case SimpleTypes.BagType(elem) =>
                    Seq(Constraint.equal(elem, rhsTpe), Constraint.equal(resultType, SimpleTypes.BagType(rhsTpe)))
                  case _ => throw new IllegalStateException("Overloading with right hand side as integer.")
                }))
                case SimpleTypes.TupleType(_) => Seq(StainlessConstraint.oneOf(lhsTpe, {
                  case ltpe: SimpleTypes.SetType => Seq(Constraint.equal(rhsTpe, ltpe.elem))
                  case ltpe: SimpleTypes.BagType => Seq(Constraint.equal(rhsTpe, ltpe.elem))
                  case ltpe: SimpleTypes.MapType => Seq(Constraint.equal(rhsTpe, SimpleTypes.TupleType(Seq(ltpe.from, ltpe.to))))
                  case _ => throw new IllegalStateException("Overloading with right hand side as tuple.")
                }))
                case _ => throw new IllegalStateException("Unifier returned unexpected value")
              }))
              .addConstraint(Constraint.equal(lhsTpe, resultType))
              .addConstraint(Constraint.equal(lhsTpe, lhsUnknown))
              .addConstraint(Constraint.equal(rhsUnknown, rhsTpe))
              .addConstraint(Constraint.exist(lhsUnknown))
              .addConstraint(Constraint.exist(rhsUnknown))
              .addConstraint(Constraint.exist(resultType))
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
