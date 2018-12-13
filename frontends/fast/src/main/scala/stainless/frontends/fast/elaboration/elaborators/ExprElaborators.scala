package stainless.frontends.fast.elaboration.elaborators

import inox.parser.elaboration
import inox.parser.elaboration.SimpleTypes

import scala.util.parsing.input.Position

trait ExprElaborators extends inox.parser.elaboration.elaborators.ExprElaborators { self: stainless.frontends.fast.Elaborators =>

  class StainlessExprE extends super.ExprE {

    override def elaborate(template: Exprs.Expr)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Expr])] = template match {
//      case Exprs.Variable(id) => {
//
//        ExprUseIdE.elaborate(id).flatMap { i =>
//          Constrained.attempt(
//            store.getFunction(i).map(x => Left(x))
//              .orElse(store.getVariable(i).map(x => Right(x))),
//            template,
//            identifierNotCallable(i.name)
//          ).flatMap {
//
//            case Left((n, f)) =>
//
//
//            case Right((st, et)) => {
//              val retTpe = SimpleTypes.Unknown.fresh.setPos(template.pos)
//              for {
//                (stas, evas) <- ExprSeqE.elaborate(args)
//                  .checkImmediate(optTypeArgs.isEmpty, template, functionValuesCanNotHaveTypeParameters(i.name))
//                  .map(_.unzip)
//                _ <- Constrained(Constraint.equal(st, SimpleTypes.FunctionType(stas, retTpe)))
//              } yield (retTpe, Eventual.withUnifier { implicit unifier =>
//                trees.Application(trees.Variable(i, et.get, Seq()), evas.map(_.get))
//              })
//            }
//          }
//        }
//      }

      case PatternMatchings.MatchExpression(lhs, cases) =>
        for {
          (tpe, eventualLhs) <- ExprE.elaborate(lhs)
          (rhsType, patternType, cases) <- MatchCaseSeqE.elaborate(cases)
          _ <- Constrained(Constraint.equal(tpe, patternType))
        } yield (rhsType, Eventual.withUnifier { implicit unifier =>
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
      case Exprs.BinaryOperation(Exprs.Binary.Plus, lhs, rhs) => {
        val resultType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val rhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val lhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val tupleFirst = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val tupleSecond = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val numericType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((resultType, Eventual.withUnifier { implicit unifier =>
              (lhsTpe, rhsTpe) match {
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
                case (SimpleTypes.BagType(tpe), elemType) if tpe == elemType =>
                  trees.BagAdd(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.MapType(from, to), SimpleTypes.TupleType(types)) if types.size == 2 && types.head == from && types(1) == to =>
                  val tupleTree = rhsEventual.get
                  trees.MapUpdated(lhsEventual.get, trees.TupleSelect(tupleTree, 1), trees.TupleSelect(tupleTree, 2))
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(SimpleTypes.FunctionType(Seq(lhsUnknown, rhsUnknown), resultType),
                  Seq(
                    SimpleTypes.FunctionType(Seq(numericType, numericType), numericType),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.StringType(), SimpleTypes.StringType()), SimpleTypes.StringType()),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(rhsUnknown), rhsUnknown), SimpleTypes.SetType(rhsUnknown)),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(rhsUnknown), rhsUnknown), SimpleTypes.BagType(rhsUnknown)),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.MapType(tupleFirst, tupleSecond), rhsUnknown), SimpleTypes.MapType(tupleFirst, tupleSecond))
                  )))
              .addConstraint(Constraint.oneOf(rhsTpe,
                Seq(
                  rhsUnknown,
                  SimpleTypes.TupleType(Seq(tupleFirst, tupleSecond)
                  ))))
              .addConstraint(Constraint.isNumeric(numericType))
              .addConstraint(Constraint.equal(lhsTpe, lhsUnknown))
              .addConstraint(Constraint.equal(lhsTpe, resultType))
              .addConstraint(Constraint.exist(resultType))
          }
        }
      }

      case Exprs.BinaryOperation(Exprs.Binary.BVAnd, lhs, rhs) =>
        val resultType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val rhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val lhsUnknown = SimpleTypes.Unknown.fresh.setPos(template.pos)
        val bitsType = SimpleTypes.Unknown.fresh.setPos(template.pos)
        ExprE.elaborate(lhs).flatMap { case (lhsTpe, lhsEventual) =>
          ExprE.elaborate(rhs).flatMap { case (rhsTpe, rhsEventual) =>
            Constrained.pure((resultType, Eventual.withUnifier { implicit unifier =>
              (lhsTpe, rhsTpe) match {
                case (SimpleTypes.BitVectorType(signed1, size1), SimpleTypes.BitVectorType(signed2, size2)) if signed1 == signed2 && size1 == size2=>
                  trees.BVAnd(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.SetType(tpe), elemType) if tpe == elemType =>
                  trees.SetIntersection(lhsEventual.get, rhsEventual.get)
                case (SimpleTypes.BagType(tpe), elemType) if tpe == elemType =>
                  trees.BagIntersection(lhsEventual.get, rhsEventual.get)
                case _ => throw new IllegalStateException("Unifier returned unexpected value.")
              }
            }))
              .addConstraint(Constraint.
                oneOf(SimpleTypes.FunctionType(Seq(lhsUnknown, rhsUnknown), resultType),
                  Seq(
                    SimpleTypes.FunctionType(Seq(bitsType, bitsType), bitsType),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(rhsUnknown), rhsUnknown), SimpleTypes.SetType(rhsUnknown)),
                    SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(rhsUnknown), rhsUnknown), SimpleTypes.BagType(rhsUnknown))
                  )))
              .addConstraint(Constraint.isBits(bitsType))
              .addConstraint(Constraint.equal(lhsTpe, lhsUnknown))
              .addConstraint(Constraint.equal(lhsTpe, resultType))
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
