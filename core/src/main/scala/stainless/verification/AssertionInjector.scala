/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

/**
 * Transform trees by inserting assertions. Those verify that all array access are valid,
 * casts are legal, no division by zero occur and, when using the [[strictArithmetic]] mode,
 * that the program is exempt of integer overflow and unexpected behaviour.
 */
trait AssertionInjector extends ast.TreeTransformer {
  val s: ast.Trees
  val t: ast.Trees

  implicit val symbols: s.Symbols

  val strictArithmetic: Boolean

  private def indexUpTo(i: t.Expr, e: t.Expr) = t.And(
    t.GreaterEquals(i, t.Int32Literal(0).copiedFrom(i)).copiedFrom(i),
    t.LessThan(i, e).copiedFrom(e)
  ).copiedFrom(i)

  override def transform(e: s.Expr): t.Expr = e match {
    case s.ArraySelect(a, i) =>
      t.Assert(
        indexUpTo(transform(i), t.ArrayLength(transform(a)).copiedFrom(a)),
        Some("Array index out of range"),
        super.transform(e)
      ).copiedFrom(e)

    case s.ArrayUpdated(a, i, v) =>
      val ta = transform(a)
      val ti = transform(i)
      t.ArrayUpdated(ta, t.Assert(
        indexUpTo(ti, t.ArrayLength(ta).copiedFrom(a)),
        Some("Array index out of range"),
        ti
      ).copiedFrom(i), transform(v)).copiedFrom(e)

    case sel @ s.ADTSelector(expr, _) =>
      t.Assert(
        t.IsConstructor(transform(expr), sel.constructor.id).copiedFrom(e),
        Some("Cast error"),
        super.transform(e)
      ).copiedFrom(e)

    case BVTyped(true, size, e0 @ s.Plus(lhs0, rhs0)) if strictArithmetic =>
      val lhs = transform(lhs0)
      val rhs = transform(rhs0)
      val newE = super.transform(e0)
      t.Assert(
        // If both operands are of the same sign, then the result should have the same sign.
        t.Implies(
          t.Equals(signBit(size, lhs), signBit(size, rhs)).copiedFrom(e),
          t.Equals(signBit(size, lhs), signBit(size, newE)).copiedFrom(e)
        ).copiedFrom(e),
        Some("Addition Overflow"),
        newE
      ).copiedFrom(e)

    // Unsigned addition
    case BVTyped(false, size, e0 @ s.Plus(lhs0, rhs0)) if strictArithmetic =>
      val lhs = transform(lhs0)
      val rhs = transform(rhs0)
      val newE = super.transform(e0)
      t.Assert(
        // the result must be greater than the lhs
        t.GreaterEquals(t.Plus(lhs, rhs), lhs).copiedFrom(e),
        Some("Addition Overflow"),
        newE
      ).copiedFrom(e)

    case BVTyped(true, size, e0 @ s.Minus(lhs0, rhs0)) if strictArithmetic =>
      val lhs = transform(lhs0)
      val rhs = transform(rhs0)
      val newE = super.transform(e0)
      t.Assert(
        // If the operands have different sign, then the result must have the same sign as the lhs.
        t.Implies(
          t.Not(t.Equals(signBit(size, lhs), signBit(size, rhs)).copiedFrom(e)).copiedFrom(e),
          t.Equals(signBit(size, lhs), signBit(size, newE)).copiedFrom(e)
        ).copiedFrom(e),
        Some("Subtraction Overflow"),
        newE
      ).copiedFrom(e)

    // Unsigned subtraction
    case BVTyped(false, size, e0 @ s.Minus(lhs0, rhs0)) if strictArithmetic =>
      val lhs = transform(lhs0)
      val rhs = transform(rhs0)
      val newE = super.transform(e0)
      t.Assert(
        // rhs must be smaller than lhs
        t.LessEquals(rhs, lhs).copiedFrom(e),
        Some("Subtraction Overflow"),
        newE
      ).copiedFrom(e)

    case BVTyped(true, size, s.UMinus(e0)) if strictArithmetic =>
      val newE = transform(e0)
      t.Assert(
        // -MinValue overflows
        t.Not(t.Equals(newE, minValue(size, e.getPos)).copiedFrom(e)).copiedFrom(e),
        Some("Negation Overflow"),
        newE
      ).copiedFrom(e)

    case BVTyped(signed, size, e0 @ s.Times(lhs0, rhs0)) if strictArithmetic =>
      val lhs = transform(lhs0)
      val rhs = transform(rhs0)
      val newE = super.transform(e0)
      t.Assert(
        // when lhs is not null, rhs === (lhs * rhs) / lhs
        t.Or(
          t.Equals(lhs, zero(signed, size, e.getPos)).copiedFrom(e),
          t.Equals(rhs, t.Division(newE, lhs).copiedFrom(e)).copiedFrom(e)
        ).copiedFrom(e),
        Some("Multiplication Overflow"),
        newE
      ).copiedFrom(e)

    case s.Division(n, d) =>
      // Check division by zero, and if requested/meaningful, check for overflow
      val newE = super.transform(e)
      val rest = e.getType match {
        case s.BVType(true, size) if strictArithmetic =>
          // Overflow happens for signed bitvectors with -MinValue / -1
          t.Assert(
            t.Not(t.And(
              t.Equals(transform(n), minValue(size, n.getPos)).copiedFrom(n),
              t.Equals(transform(d), t.BVLiteral(true, -1, size).copiedFrom(d))
            ).copiedFrom(e)).copiedFrom(e),
            Some("Division Overflow"),
            newE
          ).copiedFrom(e)

        case _ => newE
      }

      t.Assert(
        t.Not(t.Equals(transform(d), d.getType match {
          case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
          case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
          case s.RealType() => t.FractionLiteral(0, 1).copiedFrom(d)
        }).copiedFrom(d)).copiedFrom(d),
        Some("Division by zero"),
        rest
      ).copiedFrom(e)

    case s.Remainder(_, d) =>
      t.Assert(
        t.Not(t.Equals(transform(d), d.getType match {
          case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
          case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
        }).copiedFrom(d)).copiedFrom(d),
        Some("Remainder by zero"),
        super.transform(e)
      ).copiedFrom(e)

    case s.Modulo(_, d) =>
      t.Assert(
        t.Not(t.Equals(transform(d), d.getType match {
          case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
          case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
        }).copiedFrom(d)).copiedFrom(d),
        Some("Modulo by zero"),
        super.transform(e)
      ).copiedFrom(e)

    case BVTyped(signed, size, BVShift(rhs0)) if strictArithmetic =>
      val rhs = transform(rhs0)
      val newE = super.transform(e)
      val lt = t.LessThan(rhs, t.BVLiteral(signed, size, size).copiedFrom(rhs)).copiedFrom(rhs)
      // positivity check is only relevant for signed bitvectors
      val pos = t.GreaterEquals(rhs, zero(true, size, rhs.getPos)).copiedFrom(rhs)
      val range = if (signed) t.And(pos, lt).copiedFrom(rhs) else lt
      // Ensure the operation doesn't shift more bits than there are.
      t.Assert(range, Some("Shift Semantics"), newE).copiedFrom(e)

    case e: s.Ensuring => super.transform(e.toAssert)

    case _ => super.transform(e)
  }

  private object BVTyped {
    def unapply(e: s.Expr): Option[(Boolean, Int, s.Expr)] = e.getType match {
      case s.BVType(signed, size) => Some((signed, size, e))
      case _ => None
    }
  }

  private object BVShift {
    // Extract rhs of any shift operation
    def unapply(e: s.Expr): Option[s.Expr] = e match {
      case s.BVShiftLeft(_, rhs) => Some(rhs)
      case s.BVAShiftRight(_, rhs) => Some(rhs)
      case s.BVLShiftRight(_, rhs) => Some(rhs)
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
  def apply(p: Program, ctx: inox.Context): inox.ast.SymbolTransformer {
    val s: p.trees.type
    val t: p.trees.type
  } = new inox.ast.SymbolTransformer {
    val s: p.trees.type = p.trees
    val t: p.trees.type = p.trees

    def transform(syms: s.Symbols): t.Symbols = {
      object injector extends AssertionInjector {
        val s: p.trees.type = p.trees
        val t: p.trees.type = p.trees
        val symbols: p.symbols.type = p.symbols
        val strictArithmetic: Boolean =
          ctx.options.findOptionOrDefault(optStrictArithmetic)
      }

      t.NoSymbols
        .withFunctions(syms.functions.values.toSeq.map { fd =>
          val (specs, body) = s.exprOps.deconstructSpecs(fd.fullBody)(syms)
          val newSpecs = specs.map(_.map(injector.transform(_)))
          val newBody = body map injector.transform

          val resultType = injector.transform(fd.returnType)
          val fullBody = t.exprOps.reconstructSpecs(newSpecs, newBody, resultType).copiedFrom(fd.fullBody)
          new t.FunDef(
            fd.id,
            fd.tparams map injector.transform,
            fd.params map injector.transform,
            resultType,
            fullBody,
            fd.flags map injector.transform
          ).copiedFrom(fd)
        })
        .withSorts(syms.sorts.values.toSeq.map(injector.transform))
    }
  }
}
