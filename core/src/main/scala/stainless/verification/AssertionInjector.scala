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
  val t: ast.Trees

  implicit val symbols: s.Symbols

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

  private def indexUpTo(i: t.Expr, e: t.Expr) = t.And(
    t.GreaterEquals(i, t.Int32Literal(0).copiedFrom(i)).copiedFrom(i),
    t.LessThan(i, e).copiedFrom(e)
  ).copiedFrom(i)

  override def transform(e: s.Expr): t.Expr = e match {
    case s.Annotated(body, flags) if flags contains s.Wrapping =>
      t.Annotated(wrapping(true)(transform(body)), flags map transform).copiedFrom(e)

    case s.ArraySelect(a, i) =>
      val aVal = t.ValDef.fresh("a", transform(a.getType)).setPos(a)
      val iVal = t.ValDef.fresh("i", transform(i.getType)).setPos(i)
      t.Let(aVal, transform(a), t.Let(iVal, transform(i),
        t.Assert(
          indexUpTo(iVal.toVariable, t.ArrayLength(aVal.toVariable).copiedFrom(a)),
          Some("Array index out of range"),
          t.ArraySelect(aVal.toVariable, iVal.toVariable).setPos(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case s.ArrayUpdated(a, i, v) =>
      val aVal = t.ValDef.fresh("a", transform(a.getType)).setPos(a)
      val iVal = t.ValDef.fresh("i", transform(i.getType)).setPos(i)
      val vVal = t.ValDef.fresh("v", transform(v.getType)).setPos(v)
      t.Let(aVal, transform(a), t.Let(iVal, transform(i), t.Let(vVal, transform(v),
        t.Assert(
          indexUpTo(iVal.toVariable, t.ArrayLength(aVal.toVariable).copiedFrom(a)),
          Some("Array index out of range"),
          t.ArrayUpdated(aVal.toVariable, iVal.toVariable, vVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)).copiedFrom(e)

    case sel @ s.ADTSelector(expr, selector) =>
      val newExpr = transform(expr)
      t.Assert(
        t.IsConstructor(newExpr, sel.constructor.id).copiedFrom(e),
        Some("Cast error"),
        t.ADTSelector(newExpr, selector)
      ).copiedFrom(e)

    case BVTyped(true, size, e0 @ s.Plus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = t.ValDef.fresh("lhs", t.BVType(true, size)).setPos(lhs0)
      val rhsVal = t.ValDef.fresh("rhs", t.BVType(true, size)).setPos(rhs0)
      t.Let(lhsVal, transform(lhs0), t.Let(rhsVal, transform(rhs0),
        t.Assert(
          t.Implies(
            t.Equals(signBit(size, lhsVal.toVariable), signBit(size, rhsVal.toVariable)).copiedFrom(e),
            t.Equals(
              signBit(size, lhsVal.toVariable),
              signBit(size, t.Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e))
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Addition overflow"),
          t.Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    // Unsigned addition
    case BVTyped(false, size, e0 @ s.Plus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = t.ValDef.fresh("lhs", t.BVType(false, size)).setPos(lhs0)
      val rhsVal = t.ValDef.fresh("rhs", t.BVType(false, size)).setPos(rhs0)
      t.Let(lhsVal, transform(lhs0), t.Let(rhsVal, transform(rhs0),
        t.Assert(
          // the result must be greater than the lhs
          t.GreaterEquals(
            t.Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e),
            lhsVal.toVariable
          ).copiedFrom(e),
          Some("Addition overflow"),
          t.Plus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case BVTyped(true, size, e0 @ s.Minus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = t.ValDef.fresh("lhs", t.BVType(true, size)).setPos(lhs0)
      val rhsVal = t.ValDef.fresh("rhs", t.BVType(true, size)).setPos(rhs0)
      t.Let(lhsVal, transform(lhs0), t.Let(rhsVal, transform(rhs0),
        t.Assert(
          // If the operands have different sign, then the result must have the same sign as the lhs.
          t.Implies(
            t.Not(t.Equals(
              signBit(size, lhsVal.toVariable),
              signBit(size, rhsVal.toVariable)
            ).copiedFrom(e)).copiedFrom(e),
            t.Equals(
              signBit(size, lhsVal.toVariable),
              signBit(size, t.Minus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e))
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Subtraction overflow"),
          t.Minus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    // Unsigned subtraction
    case BVTyped(false, size, e0 @ s.Minus(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = t.ValDef.fresh("lhs", t.BVType(false, size)).setPos(lhs0)
      val rhsVal = t.ValDef.fresh("rhs", t.BVType(false, size)).setPos(rhs0)
      t.Let(lhsVal, transform(lhs0), t.Let(rhsVal, transform(rhs0),
        t.Assert(
          // rhs must be smaller than lhs
          t.LessEquals(rhsVal.toVariable, lhsVal.toVariable).copiedFrom(e),
          Some("Subtraction overflow"),
          t.Minus(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case BVTyped(true, size, e0 @ s.UMinus(n0)) if checkOverflow =>
      val innerVal = t.ValDef.fresh("inner", t.BVType(true, size))
      t.Let(innerVal, transform(n0),
        t.Assert(
          // -MinValue overflows
          t.Not(t.Equals(innerVal.toVariable, minValue(size, e.getPos)).copiedFrom(e)).copiedFrom(e),
          Some("Negation overflow"),
          t.UMinus(innerVal.toVariable)
        ).copiedFrom(e)
      ).copiedFrom(e)

    case BVTyped(signed, size, e0 @ s.Times(lhs0, rhs0)) if checkOverflow =>
      val lhsVal = t.ValDef.fresh("lhs", t.BVType(signed, size)).setPos(lhs0)
      val rhsVal = t.ValDef.fresh("rhs", t.BVType(signed, size)).setPos(rhs0)
      t.Let(lhsVal, transform(lhs0), t.Let(rhsVal, transform(rhs0),
        t.Assert(
          // when lhs is not null, rhs === (lhs * rhs) / lhs
          t.Or(
            t.Equals(lhsVal.toVariable, zero(signed, size, e.getPos)).copiedFrom(e),
            t.Equals(
              rhsVal.toVariable,
              t.Division(
                t.Times(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e),
                lhsVal.toVariable
              ).copiedFrom(e)
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Multiplication overflow"),
          t.Times(lhsVal.toVariable, rhsVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case s.Division(n, d) =>
      // Check division by zero, and if requested/meaningful, check for overflow
      val nVal = t.ValDef.fresh("n", transform(n.getType)).setPos(n)
      val dVal = t.ValDef.fresh("d", transform(d.getType)).setPos(d)

      val rest = e.getType match {
        case s.BVType(true, size) if checkOverflow =>
          // Overflow happens for signed bitvectors with -MinValue / -1
          t.Assert(
            t.Not(t.And(
              t.Equals(nVal.toVariable, minValue(size, n.getPos)).copiedFrom(n),
              t.Equals(dVal.toVariable, t.BVLiteral(true, -1, size).copiedFrom(d))
            ).copiedFrom(e)).copiedFrom(e),
            Some("Division overflow"),
            t.Division(nVal.toVariable, dVal.toVariable).copiedFrom(e)
          ).copiedFrom(e)

        case _ =>
          t.Division(nVal.toVariable, dVal.toVariable).copiedFrom(e)

      }

      t.Let(nVal, transform(n), t.Let(dVal, transform(d),
        t.Assert(
          t.Not(t.Equals(dVal.toVariable, d.getType match {
            case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
            case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
            case s.RealType() => t.FractionLiteral(0, 1).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Division by zero"),
          rest
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case s.Remainder(n, d) =>
      val nVal = t.ValDef.fresh("n", transform(n.getType)).setPos(n)
      val dVal = t.ValDef.fresh("d", transform(d.getType)).setPos(d)
      t.Let(nVal, transform(n), t.Let(dVal, transform(d),
        t.Assert(
          t.Not(t.Equals(dVal.toVariable, d.getType match {
            case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
            case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Remainder by zero"),
          t.Remainder(nVal.toVariable, dVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case s.Modulo(n, d) =>
      val nVal = t.ValDef.fresh("n", transform(n.getType)).setPos(n)
      val dVal = t.ValDef.fresh("d", transform(d.getType)).setPos(d)
      t.Let(nVal, transform(n), t.Let(dVal, transform(d),
        t.Assert(
          t.Not(t.Equals(dVal.toVariable, d.getType match {
            case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
            case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Modulo by zero"),
          t.Modulo(nVal.toVariable, dVal.toVariable).copiedFrom(e)
        ).copiedFrom(e)
      ).copiedFrom(e)).copiedFrom(e)

    case BVTyped(signed, size, BVShift(rhs, recons)) if strictArithmetic =>
      val rhsVal = t.ValDef.fresh("rhs", transform(rhs.getType)).setPos(rhs)
      val lt = t.LessThan(rhsVal.toVariable, t.BVLiteral(signed, size, size).copiedFrom(rhs)).copiedFrom(rhs)
      // positivity check is only relevant for signed bitvectors
      val pos = t.GreaterEquals(rhsVal.toVariable, zero(true, size, rhs.getPos)).copiedFrom(rhs)
      val range = if (signed && checkOverflow) t.And(pos, lt).copiedFrom(rhs) else lt
      // Ensure the operation doesn't shift more bits than there are.
      t.Let(rhsVal, transform(rhs),
        t.Assert(range, Some("Shift semantics"), recons(rhsVal.toVariable)).copiedFrom(e)
      ).copiedFrom(e)

    case _ => super.transform(e)
  }

  private object BVTyped {
    def unapply(e: s.Expr): Option[(Boolean, Int, s.Expr)] = e.getType match {
      case s.BVType(signed, size) => Some((signed, size, e))
      case _ => None
    }
  }

  private object BVShift {
    // Extract rhs of any shift operation, and return a reconstructor
    def unapply(e: s.Expr): Option[(s.Expr, t.Expr => t.Expr)] = e match {
      case s.BVShiftLeft(lhs, rhs) => Some((rhs, (r: t.Expr) => t.BVShiftLeft(transform(lhs), r).copiedFrom(e)))
      case s.BVAShiftRight(lhs, rhs) => Some((rhs, (r: t.Expr) => t.BVAShiftRight(transform(lhs), r).copiedFrom(e)))
      case s.BVLShiftRight(lhs, rhs) => Some((rhs, (r: t.Expr) => t.BVLShiftRight(transform(lhs), r).copiedFrom(e)))
      case _ => None
    }
  }

  private def signBit(size: Int, e: t.Expr): t.Expr = {
    val mask = t.BVLiteral(true, BigInt(1) << (size - 1), size).copiedFrom(e)
    val sign = t.BVAnd(e, mask).copiedFrom(e)
    sign
  }

  private def minValue(size: Int, pos: inox.utils.Position) =
    t.BVLiteral(true, -BigInt(2).pow(size - 1), size).setPos(pos)

  private def zero(signed: Boolean, size: Int, pos: inox.utils.Position) =
    t.BVLiteral(signed, 0, size).setPos(pos)
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
