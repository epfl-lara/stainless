package stainless.frontends.fast
import org.scalatest._

class ElaboratorsTests extends FunSuite
  with stainless.frontends.fast.Elaborators
{


  val plusSequence = (rhsType: SimpleTypes.Type, tupleType: SimpleTypes.TupleType) => Seq(
    SimpleTypes.FunctionType(Seq(SimpleTypes.IntegerType(), SimpleTypes.IntegerType()), SimpleTypes.IntegerType()),
    SimpleTypes.FunctionType(Seq(SimpleTypes.StringType(), SimpleTypes.StringType()), SimpleTypes.StringType()),
    SimpleTypes.FunctionType(Seq(SimpleTypes.RealType(), SimpleTypes.RealType()), SimpleTypes.RealType()),
    SimpleTypes.FunctionType(Seq(SimpleTypes.BitVectorType(true, 32), SimpleTypes.BitVectorType(true, 32)), SimpleTypes.BitVectorType(true, 32)),
    SimpleTypes.FunctionType(Seq(SimpleTypes.SetType(rhsType), rhsType), SimpleTypes.SetType(rhsType)),
    SimpleTypes.FunctionType(Seq(SimpleTypes.BagType(rhsType), rhsType), SimpleTypes.BagType(rhsType)),
    SimpleTypes.FunctionType(Seq(SimpleTypes.MapType(tupleType.elems.head, tupleType.elems(1)), rhsType),
      SimpleTypes.MapType(tupleType.elems.head, tupleType.elems(1)))
  )

  test("simple test") {
    val rhsTpe = SimpleTypes.BitVectorType(true, 32)
    val lhsTpe = SimpleTypes.SetType(SimpleTypes.BitVectorType(true, 32))

    val resultType = SimpleTypes.Unknown.fresh
    val rhsUnknown = SimpleTypes.Unknown.fresh
    val lhsUnknown = SimpleTypes.Unknown.fresh
    val operatorType = SimpleTypes.FunctionType(Seq(lhsUnknown, rhsUnknown), resultType)
    val operatorTypeUnknown = SimpleTypes.Unknown.fresh
    val tupleFirst = SimpleTypes.Unknown.fresh
    val tupleSecond = SimpleTypes.Unknown.fresh


    val constraints = Seq(StainlessConstraint.
      oneOf(operatorType, plusSequence(rhsUnknown, SimpleTypes.TupleType(Seq(tupleFirst, tupleSecond)))),
      StainlessConstraint.option(rhsTpe, SimpleTypes.TupleType(Seq(tupleFirst, tupleSecond))),
      Constraint.equal(lhsTpe, resultType),
      Constraint.equal(lhsTpe, lhsUnknown),
      Constraint.equal(rhsUnknown, rhsTpe),
      Constraint.exist(rhsUnknown),
      Constraint.exist(resultType),
      Constraint.equal(operatorType, operatorTypeUnknown)
    )

    val result = solve(constraints)

    result match {
      case Right(unifier) =>
        val result = unifier.get(resultType)
        val operatorType = unifier.get(operatorTypeUnknown)
        val lhsType = unifier.get(lhsUnknown)
        val rhsType = unifier.get(rhsUnknown)

        assert(result == SimpleTypes.SetType(SimpleTypes.BitVectorType(true, 32)))
        assert(rhsType == SimpleTypes.BitVectorType(true, 32))
        assert(lhsType == SimpleTypes.SetType(SimpleTypes.BitVectorType(true, 32)))
        assert(operatorType == SimpleTypes.FunctionType(
          Seq(
            SimpleTypes.SetType(SimpleTypes.BitVectorType(true, 32)),
            SimpleTypes.BitVectorType(true, 32)
          ),
          SimpleTypes.SetType(SimpleTypes.BitVectorType(true, 32))))
      case Left(errorMessage) => fail(errorMessage)
    }
  }
}
