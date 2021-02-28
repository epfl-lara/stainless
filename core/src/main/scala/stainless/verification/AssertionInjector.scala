/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

/**
 * Transform trees by inserting assertions. Those verify that all array access are valid,
 * casts are legal, no division by zero occur and, when using the [[strictArithmetic]] mode,
 * that the program is exempt of integer overflow and unexpected behaviour.
 */
trait AssertionInjector extends transformers.TreeTransformer {
  val s: ast.Trees
  val t: s.type

  import s._

  implicit val symbols: Symbols

  val strictArithmetic: Boolean

  private[this] var inWrappingMode: Boolean = false
  private[this] def checkOverflow: Boolean = strictArithmetic && !inWrappingMode

  def wrapping[A](enabled: Boolean)(a: => A): A = {
    val old = inWrappingMode
    inWrappingMode = enabled
    val res = a
    inWrappingMode = old
    res
  }

  private def indexUpTo(i: Expr, e: Expr) = And(
    GreaterEquals(i, Int32Literal(0).copiedFrom(i)).copiedFrom(i),
    LessThan(i, e).copiedFrom(e)
  ).copiedFrom(i)

  override def transform(e: Expr): Expr = e match {
    case Annotated(body, flags) if flags contains Wrapping =>
      Annotated(wrapping(true)(transform(body)), flags map transform).copiedFrom(e)

    case ArraySelect(a, i) =>
      val aVal = ValDef.fresh("a", a.getType).setPos(a)
      val iVal = ValDef.fresh("i", i.getType).setPos(i)
      Let(aVal, transform(a), Let(iVal, transform(i),
        Assert(
          indexUpTo(iVal.toVariable, ArrayLength(aVal.toVariable).copiedFrom(a)),
          Some("Array index out of range"),
          ArraySelect(aVal.toVariable, iVal.toVariable).setPos(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case ArrayUpdated(a, i, v) =>
      val aVal = ValDef.fresh("a", a.getType).setPos(a)
      val iVal = ValDef.fresh("i", i.getType).setPos(i)
      val vVal = ValDef.fresh("v", v.getType).setPos(v)
      Let(aVal, transform(a), Let(iVal, transform(i), Let(vVal, transform(v),
        Assert(
          indexUpTo(iVal.toVariable, ArrayLength(aVal.toVariable).copiedFrom(a)),
          Some("Array index out of range"),
          ArrayUpdated(aVal.toVariable, iVal.toVariable, vVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)).copiedFrom(e)

    case sel @ ADTSelector(adt, sid) =>
      val adtVal = ValDef.fresh("adt", adt.getType).setPos(adt)
      Let(adtVal, transform(adt),
        Assert(
          IsConstructor(adtVal.toVariable, sel.constructor.id).copiedFrom(e),
          Some("Cast error"),
          ADTSelector(adtVal.toVariable, sid).copiedFrom(sel)
        ).copiedFrom(e)
      ).copiedFrom(e)

    case BVTyped(true, size, e0 @ Plus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = ValDef.fresh("lhs", BVType(true, size)).setPos(lhs0)
      val rhsVal = ValDef.fresh("rhs", BVType(true, size)).setPos(rhs0)
      Let(lhsVal, transform(lhs0), Let(rhsVal, transform(rhs0),
        Assert(
          Implies(
            Equals(signBit(size, lhsVal.toVariable), signBit(size, rhsVal.toVariable)).copiedFrom(e),
            Equals(
              signBit(size, lhsVal.toVariable),
              signBit(size, Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e))
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Addition overflow"),
          Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    // Unsigned addition
    case BVTyped(false, size, e0 @ Plus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = ValDef.fresh("lhs", BVType(false, size)).setPos(lhs0)
      val rhsVal = ValDef.fresh("rhs", BVType(false, size)).setPos(rhs0)
      Let(lhsVal, transform(lhs0), Let(rhsVal, transform(rhs0),
        Assert(
          // the result must be greater than the lhs
          GreaterEquals(
            Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e),
            lhsVal.toVariable
          ).copiedFrom(e),
          Some("Addition overflow"),
          Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case BVTyped(true, size, e0 @ Minus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = ValDef.fresh("lhs", BVType(true, size)).setPos(lhs0)
      val rhsVal = ValDef.fresh("rhs", BVType(true, size)).setPos(rhs0)
      Let(lhsVal, transform(lhs0), Let(rhsVal, transform(rhs0),
        Assert(
          // If the operands have different sign, then the result must have the same sign as the lhs.
          Implies(
            Not(Equals(
              signBit(size, lhsVal.toVariable),
              signBit(size, rhsVal.toVariable)
            ).copiedFrom(e)).copiedFrom(e),
            Equals(
              signBit(size, lhsVal.toVariable),
              signBit(size, Minus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e))
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Subtraction overflow"),
          Minus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    // Unsigned subtraction
    case BVTyped(false, size, e0 @ Minus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = ValDef.fresh("lhs", BVType(false, size)).setPos(lhs0)
      val rhsVal = ValDef.fresh("rhs", BVType(false, size)).setPos(rhs0)
      Let(lhsVal, transform(lhs0), Let(rhsVal, transform(rhs0),
        Assert(
          // rhs must be smaller than lhs
          LessEquals(rhsVal.toVariable, lhsVal.toVariable).copiedFrom(e),
          Some("Subtraction overflow"),
          Minus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case BVTyped(true, size, e0 @ UMinus(n0)) if checkOverflow =>
      val innerVal = ValDef.fresh("inner", BVType(true, size))
      Let(innerVal, transform(n0),
        Assert(
          // -MinValue overflows
          Not(Equals(innerVal.toVariable, minValue(size, e.getPos)).copiedFrom(e)).copiedFrom(e),
          Some("Negation overflow"),
          UMinus(innerVal.toVariable)
        ).copiedFrom(e)
      ).copiedFrom(e)

    case BVTyped(signed, size, e0 @ Times(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = ValDef.fresh("lhs", BVType(signed, size)).setPos(lhs0)
      val rhsVal = ValDef.fresh("rhs", BVType(signed, size)).setPos(rhs0)
      Let(lhsVal, transform(lhs0), Let(rhsVal, transform(rhs0),
        Assert(
          // when lhs is not null, rhs === (lhs * rhs) / lhs
          Or(
            Equals(lhsVal.toVariable, zero(signed, size, e.getPos)).copiedFrom(e),
            Equals(
              rhsVal.toVariable,
              Division(
                Times(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e),
                lhsVal.toVariable
              ).copiedFrom(e)
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Multiplication overflow"),
          Times(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case Division(n, d) =>
      // Check division by zero, and if requested/meaningful, check for overflow
      val nVal = ValDef.fresh("n", n.getType).setPos(n)
      val dVal = ValDef.fresh("d", d.getType).setPos(d)

      val rest = e.getType match {
        case BVType(true, size) if checkOverflow =>
          // Overflow happens for signed bitvectors with -MinValue / -1
          Assert(
            Not(And(
              Equals(nVal.toVariable, minValue(size, n.getPos)).copiedFrom(n),
              Equals(dVal.toVariable, BVLiteral(true, -1, size).copiedFrom(d))
            ).copiedFrom(e)).copiedFrom(e),
            Some("Division overflow"),
            Division(nVal.toVariable, dVal.toVariable).copiedFrom(e)
          ).copiedFrom(e)

        case _ =>
          Division(nVal.toVariable, dVal.toVariable).copiedFrom(e)

      }

      Let(nVal, transform(n), Let(dVal, transform(d),
        Assert(
          Not(Equals(dVal.toVariable, d.getType match {
            case IntegerType() => IntegerLiteral(0).copiedFrom(d)
            case BVType(signed, i) => BVLiteral(signed, 0, i).copiedFrom(d)
            case RealType() => FractionLiteral(0, 1).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Division by zero"),
          rest
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case Remainder(n, d) =>
      val nVal = ValDef.fresh("n", n.getType).setPos(n)
      val dVal = ValDef.fresh("d", d.getType).setPos(d)
      Let(nVal, transform(n), Let(dVal, transform(d),
        Assert(
          Not(Equals(dVal.toVariable, d.getType match {
            case IntegerType() => IntegerLiteral(0).copiedFrom(d)
            case BVType(signed, i) => BVLiteral(signed, 0, i).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Remainder by zero"),
          Remainder(nVal.toVariable, dVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case Modulo(n, d) =>
      val nVal = ValDef.fresh("n", n.getType).setPos(n)
      val dVal = ValDef.fresh("d", d.getType).setPos(d)
      Let(nVal, transform(n), Let(dVal, transform(d),
        Assert(
          Not(Equals(dVal.toVariable, d.getType match {
            case IntegerType() => IntegerLiteral(0).copiedFrom(d)
            case BVType(signed, i) => BVLiteral(signed, 0, i).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Modulo by zero"),
          Modulo(nVal.toVariable, dVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case BVTyped(signed, size, BVShift(rhs, recons)) if strictArithmetic =>
      val rhsVal = ValDef.fresh("rhs", rhs.getType).setPos(rhs)
      val lt = LessThan(rhsVal.toVariable, BVLiteral(signed, size, size).copiedFrom(rhs)).copiedFrom(rhs)
      // positivity check is only relevant for signed bitvectors
      val pos = GreaterEquals(rhsVal.toVariable, zero(true, size, rhs.getPos)).copiedFrom(rhs)
      val range = if (signed && checkOverflow) And(pos, lt).copiedFrom(rhs) else lt
      // Ensure the operation doesn't shift more bits than there are.
      Let(rhsVal, transform(rhs),
        Assert(range, Some("Shift semantics"), recons(rhsVal.toVariable)).copiedFrom(e)
      ).copiedFrom(e)

    case _ => super.transform(e)
  }

  private object BVTyped {
    def unapply(e: Expr): Option[(Boolean, Int, Expr)] = e.getType match {
      case BVType(signed, size) => Some((signed, size, e))
      case _ => None
    }
  }

  private object BVShift {
    // Extract rhs of any shift operation, and return a reconstructor
    def unapply(e: Expr): Option[(Expr, Expr => Expr)] = e match {
      case BVShiftLeft(lhs, rhs) => Some(rhs, r => BVShiftLeft(lhs, r).copiedFrom(e))
      case BVAShiftRight(lhs, rhs) => Some(rhs, r => BVAShiftRight(lhs, r).copiedFrom(e))
      case BVLShiftRight(lhs, rhs) => Some(rhs, r => BVLShiftRight(lhs, r).copiedFrom(e))
      case _ => None
    }
  }

  private def signBit(size: Int, e: Expr): Expr = {
    val mask = BVLiteral(true, BigInt(1) << (size - 1), size).copiedFrom(e)
    val sign = BVAnd(e, mask).copiedFrom(e)
    sign
  }

  private def minValue(size: Int, pos: inox.utils.Position) =
    BVLiteral(true, -BigInt(2).pow(size - 1), size).setPos(pos)

  private def zero(signed: Boolean, size: Int, pos: inox.utils.Position) =
    BVLiteral(signed, 0, size).setPos(pos)
}

object AssertionInjector {
  def apply(p: Program, ctx: inox.Context): inox.transformers.SymbolTransformer {
    val s: p.trees.type
    val t: p.trees.type
  } = new inox.transformers.SymbolTransformer {
    val s: p.trees.type = p.trees
    val t: p.trees.type = p.trees

    import s._

    def transform(syms: Symbols): Symbols = {
      object injector extends AssertionInjector {
        val s: p.trees.type = p.trees
        val t: p.trees.type = p.trees
        val symbols: p.symbols.type = p.symbols
        val strictArithmetic: Boolean = ctx.options.findOptionOrDefault(optStrictArithmetic)
      }

      NoSymbols
        .withFunctions(syms.functions.values.toSeq.map { fd =>
          injector.wrapping(fd.flags.contains(s.Wrapping)) {
            new FunDef(
              fd.id,
              fd.tparams map injector.transform,
              fd.params map injector.transform,
              injector.transform(fd.returnType),
              injector.transform(fd.fullBody),
              fd.flags map injector.transform
            ).copiedFrom(fd)
          }
        })
        .withSorts(syms.sorts.values.toSeq.map(injector.transform))
    }
  }
}
