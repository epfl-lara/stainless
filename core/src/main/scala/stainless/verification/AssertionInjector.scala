/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

/**
 * Transform trees by inserting assertions. Those verify that all array access are valid,
 * casts are legal, no division by zero occur and, when using the [[strictArithmetic]] mode,
 * that the program is exempt of integer overflow and unexpected behaviour.
 */
class AssertionInjector(override val s: ast.Trees, override val t: ast.Trees, val strictArithmetic: Boolean)
                       (using val symbols: s.Symbols)
  extends transformers.ConcreteTreeTransformer(s, t) {

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

  // small terms that can be duplicated without code or VCs explosion
  private def canDuplicate(e: s.Expr): Boolean = e match {
    case s.Annotated(body, flags) => canDuplicate(body)
    case _: s.BVLiteral => true
    case _: s.IntegerLiteral => true
    case _: s.StringLiteral => true
    case _: s.Variable => true
    case s.Tuple(es) => es.forall(canDuplicate)
    case _ => false
  }

  private def bindIfCannotDuplicate(e: s.Expr, name: String)(f: t.Expr => t.Expr): t.Expr = {
    if (canDuplicate(e)) f(transform(e))
    else {
      val x = t.ValDef.fresh(name, transform(e.getType)).setPos(e)
      t.Let(x, transform(e), f(x.toVariable)).setPos(e)
    }
  }

  override def transform(e: s.Expr): t.Expr = e match {
    case s.Annotated(body, flags) if flags contains s.Wrapping =>
      t.Annotated(wrapping(true)(transform(body)), flags map transform).copiedFrom(e)

    case s.ArraySelect(a, i) =>
      bindIfCannotDuplicate(a, "a") { ax =>
      bindIfCannotDuplicate(i, "i") { ix =>
        t.Assert(
          indexUpTo(ix, t.ArrayLength(ax).copiedFrom(a)),
          Some("Array index out of range"),
          t.ArraySelect(ax, ix).setPos(e)
        ).copiedFrom(e)
      }}

    case s.ArrayUpdated(a, i, v) =>
      bindIfCannotDuplicate(a, "a") { ax =>
      bindIfCannotDuplicate(i, "i") { ix =>
      bindIfCannotDuplicate(v, "v") { vx =>
        t.Assert(
          indexUpTo(ix, t.ArrayLength(ax).copiedFrom(a)),
          Some("Array index out of range"),
          t.ArrayUpdated(ax, ix, vx).copiedFrom(e)
        ).copiedFrom(e)
      }}}

    case sel @ s.ADTSelector(recv, selector) =>
      if (sel.constructor.sort.constructors.size == 1)
        t.ADTSelector(transform(recv), selector).copiedFrom(e)
      else
        bindIfCannotDuplicate(recv, "recv") { recvx =>
          t.Assert(
            t.IsConstructor(recvx, sel.constructor.id).copiedFrom(e),
            Some("Cast error"),
            t.ADTSelector(recvx, selector)
          ).copiedFrom(e)
        }

    case BVTyped(true, size, e0 @ s.Plus(lhs0, rhs0)) if checkOverflow =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        t.Assert(
          t.Implies(
            t.Equals(signBit(size, lhsx), signBit(size, rhsx)).copiedFrom(e),
            t.Equals(
              signBit(size, lhsx),
              signBit(size, t.Plus(lhsx, rhsx).copiedFrom(e))
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Addition overflow"),
          t.Plus(lhsx, rhsx).copiedFrom(e)
        ).copiedFrom(e)
      }}

    // Unsigned addition
    case BVTyped(false, size, e0 @ s.Plus(lhs0, rhs0)) if checkOverflow =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        t.Assert(
          // the result must be greater than the lhs
          t.GreaterEquals(
            t.Plus(lhsx, rhsx).copiedFrom(e),
            lhsx
          ).copiedFrom(e),
          Some("Addition overflow"),
          t.Plus(lhsx, rhsx).copiedFrom(e)
        ).copiedFrom(e)
      }}

    case BVTyped(true, size, e0 @ s.Minus(lhs0, rhs0)) if checkOverflow =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        t.Assert(
          // If the operands have different sign, then the result must have the same sign as the lhs.
          t.Implies(
            t.Not(t.Equals(
              signBit(size, lhsx),
              signBit(size, rhsx)
            ).copiedFrom(e)).copiedFrom(e),
            t.Equals(
              signBit(size, lhsx),
              signBit(size, t.Minus(lhsx, rhsx).copiedFrom(e))
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Subtraction overflow"),
          t.Minus(lhsx, rhsx).copiedFrom(e)
        ).copiedFrom(e)
      }}

    // Unsigned subtraction
    case BVTyped(false, size, e0 @ s.Minus(lhs0, rhs0)) if checkOverflow =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        t.Assert(
          // rhs must be smaller than lhs
          t.LessEquals(rhsx, lhsx).copiedFrom(e),
          Some("Subtraction overflow"),
          t.Minus(lhsx, rhsx).copiedFrom(e)
        ).copiedFrom(e)
      }}

    case BVTyped(true, size, e0 @ s.UMinus(n0)) if checkOverflow =>
      bindIfCannotDuplicate(n0, "inner") { innerx =>
        t.Assert(
          // -MinValue overflows
          t.Not(t.Equals(innerx, minValue(size, e.getPos)).copiedFrom(e)).copiedFrom(e),
          Some("Negation overflow"),
          t.UMinus(innerx)
        ).copiedFrom(e)
      }

    case BVTyped(signed, size, e0 @ s.Times(lhs0, rhs0)) if checkOverflow =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        t.Assert(
          // when lhs is not null, rhs === (lhs * rhs) / lhs
          t.Or(
            t.Equals(lhsx, zero(signed, size, e.getPos)).copiedFrom(e),
            t.Equals(
              rhsx,
              t.Division(
                t.Times(lhsx, rhsx).copiedFrom(e),
                lhsx
              ).copiedFrom(e)
            ).copiedFrom(e)
          ).copiedFrom(e),
          Some("Multiplication overflow"),
          t.Times(lhsx, rhsx).copiedFrom(e)
        ).copiedFrom(e)
      }}

    case s.Division(n, d) =>
      // Check division by zero, and if requested/meaningful, check for overflow
      bindIfCannotDuplicate(n, "n") { nx =>
      bindIfCannotDuplicate(d, "d") { dx =>

        val rest = e.getType match {
          case s.BVType(true, size) if checkOverflow =>
            // Overflow happens for signed bitvectors with -MinValue / -1
            t.Assert(
              t.Not(t.And(
                t.Equals(nx, minValue(size, n.getPos)).copiedFrom(n),
                t.Equals(dx, t.BVLiteral(true, -1, size).copiedFrom(d))
              ).copiedFrom(e)).copiedFrom(e),
              Some("Division overflow"),
              t.Division(nx, dx).copiedFrom(e)
            ).copiedFrom(e)

          case _ =>
            t.Division(nx, dx).copiedFrom(e)

        }

        t.Assert(
          t.Not(t.Equals(dx, d.getType match {
            case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
            case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
            case s.RealType() => t.FractionLiteral(0, 1).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Division by zero"),
          rest
        ).copiedFrom(e)
      }}

    case s.Remainder(n, d) =>
      bindIfCannotDuplicate(n, "n") { nx =>
      bindIfCannotDuplicate(d, "d") { dx =>
        t.Assert(
          t.Not(t.Equals(dx, d.getType match {
            case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
            case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Remainder by zero"),
          t.Remainder(nx, dx).copiedFrom(e)
        ).copiedFrom(e)
      }}

    case s.Modulo(n, d) =>
      bindIfCannotDuplicate(n, "n") { nx =>
      bindIfCannotDuplicate(d, "d") { dx =>
        t.Assert(
          t.Not(t.Equals(dx, d.getType match {
            case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
            case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
          }).copiedFrom(d)).copiedFrom(d),
          Some("Modulo by zero"),
          t.Modulo(nx, dx).copiedFrom(e)
        ).copiedFrom(e)
      }}

    case s.BVUnsignedToSigned(BVTyped(signed, size, bv)) if checkOverflow =>
      assert(!signed)
      bindIfCannotDuplicate(bv, "bv") { x =>
        t.Assert(
          t.LessThan(x, t.BVLiteral(false, BigInt(2) pow (size-1), size).copiedFrom(e)).copiedFrom(e),
          Some("Unsigned to signed overflow"),
          t.BVUnsignedToSigned(x).copiedFrom(e)
        ).copiedFrom(e)
      }

    case s.BVSignedToUnsigned(BVTyped(signed, size, bv)) if checkOverflow =>
      assert(signed)
      bindIfCannotDuplicate(bv, "bv") { x =>
        t.Assert(
          t.GreaterEquals(x, t.BVLiteral(true, 0, size).copiedFrom(e)).copiedFrom(e),
          Some("Signed to unsigned requires >= 0"),
          t.BVSignedToUnsigned(x).copiedFrom(e)
        ).copiedFrom(e)
      }

    case s.BVNarrowingCast(BVTyped(signed1, size1, bv), newType) if checkOverflow =>
      val s.BVType(signed2, size2) = newType
      assert(signed1 == signed2)
      assert(size2 < size1)
      if (!signed1) {
        bindIfCannotDuplicate(bv, "bv") { x =>
          t.Assert(
            t.LessThan(x, t.BVLiteral(false, BigInt(2).pow(size2), size1).copiedFrom(e)).copiedFrom(e),
            Some("Narrowing too large unsigned int"),
            t.BVNarrowingCast(x, t.BVType(signed2, size2).copiedFrom(e)).copiedFrom(e)
          ).copiedFrom(e)
        }
      } else {
        bindIfCannotDuplicate(bv, "bv") { x =>
          t.Assert(
            t.LessThan(x, t.BVLiteral(true, BigInt(2).pow(size2-1), size1).copiedFrom(e)).copiedFrom(e),
            Some("Narrowing too large signed int"),
            t.Assert(
              t.GreaterEquals(x, t.BVLiteral(true, -BigInt(2).pow(size2-1), size1).copiedFrom(e)).copiedFrom(e),
              Some("Narrowing large negative signed int"),
              t.BVNarrowingCast(x, t.BVType(signed2, size2).copiedFrom(e)).copiedFrom(e)
            ).copiedFrom(e)
          ).copiedFrom(e)
        }
      }

    case BVTyped(signed, size, BVShift(rhs, recons)) if strictArithmetic =>
      bindIfCannotDuplicate(rhs, "rhs") { rhsx =>
        val leq = t.LessEquals(rhsx, t.BVLiteral(signed, size, size).copiedFrom(rhs)).copiedFrom(rhs)
        // positivity check is only relevant for signed bitvectors
        val pos = t.GreaterEquals(rhsx, zero(true, size, rhs.getPos)).copiedFrom(rhs)
        // TODO: explain why `checkOverflow` here and `strictArithmetic` in the guard?
        val range = if (signed && checkOverflow) t.And(pos, leq).copiedFrom(rhs) else leq
        // Ensure the operation doesn't shift more bits than there are.
        t.Assert(range, Some("Shift semantics"), recons(rhsx)).copiedFrom(e)
      }

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
  } = {
    class InjectorImpl(override val s: p.trees.type,
                       override val t: p.trees.type)
                      (using override val symbols: p.symbols.type)
      extends AssertionInjector(s, t, ctx.options.findOptionOrDefault(optStrictArithmetic))
    val injector = new InjectorImpl(p.trees, p.trees)(using p.symbols)

    class TransformerImpl(override val s: p.trees.type, override val t: p.trees.type)
      extends inox.transformers.SymbolTransformer {
      import s._

      def transform(syms: Symbols): Symbols = {
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

    new TransformerImpl(p.trees, p.trees)
  }
}
