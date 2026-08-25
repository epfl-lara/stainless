/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import smtlib.theories.FloatingPoint.FPLit

/**
 * Transform trees by inserting assertions. Those verify that all array access are valid,
 * casts are legal, no division by zero occur and, when using the [[strictArithmetic]] mode,
 * that the program is exempt of integer overflow and unexpected behaviour.
 */
class AssertionInjector(override val s: ast.Trees, override val t: ast.Trees,
                        val strictArithmetic: Boolean, val bigIntToUInt32: Boolean = false)
                       (using val symbols: s.Symbols)
  extends transformers.ConcreteTreeTransformer(s, t) {

  private var inWrappingMode: Boolean = false
  private def checkOverflow: Boolean = strictArithmetic && !inWrappingMode

  def wrapping[A](enabled: Boolean)(a: => A): A = {
    val old = inWrappingMode
    inWrappingMode = enabled
    val res = a
    inWrappingMode = old
    res
  }

  // BigInt bounds checks (--genc-bigint-as=uint32) do not apply inside specs and ghost code:
  // GenC never compiles those, and proofs legitimately use unbounded arithmetic there.
  // Unlike checkOverflow, wrapping mode does not disable these checks, as "wrapping BigInt"
  // would silently change the mathematical semantics of the compiled program.
  private var inSpecOrGhost: Boolean = false
  private def bigIntCheck: Boolean = bigIntToUInt32 && !inSpecOrGhost

  def specOrGhost[A](enabled: Boolean)(a: => A): A = {
    val old = inSpecOrGhost
    inSpecOrGhost = enabled
    val res = a
    inSpecOrGhost = old
    res
  }

  private def inSpec[A](a: => A): A = specOrGhost(true)(a)

  private val uint32Max = BigInt(2).pow(32) - 1

  private def assertInUInt32Range(res: t.Expr, what: String, e: s.Expr): t.Expr =
    t.Assert(
      t.And(
        t.LessEquals(t.IntegerLiteral(BigInt(0)).copiedFrom(e), res).copiedFrom(e),
        t.LessEquals(res, t.IntegerLiteral(uint32Max).copiedFrom(e)).copiedFrom(e)
      ).copiedFrom(e),
      Some(what),
      res
    ).copiedFrom(e)

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
    case _: s.FPLiteral => true
    case s.Tuple(es) => es.forall(canDuplicate)
    case _ => false
  }

  private def bindIfCannotDuplicate(e: s.Expr, name: String)(f: t.Expr => t.Expr): t.Expr = {
    if (canDuplicate(e)) f(transform(e)).setPos(e)
    else {
      val x = t.ValDef.fresh(name, transform(e.getType)).setPos(e)
      t.Let(x, transform(e), f(x.toVariable)).setPos(e)
    }
  }

  override def transform(e: s.Expr): t.Expr = e match {
    case s.Annotated(body, flags) if (flags contains s.Wrapping) || (flags contains s.Ghost) =>
      val inner = wrapping(inWrappingMode || (flags contains s.Wrapping)) {
        specOrGhost(inSpecOrGhost || (flags contains s.Ghost)) {
          transform(body)
        }
      }
      t.Annotated(inner, flags map transform).copiedFrom(e)

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

    case s.LargeArray(elems, default, size, base) =>
      val recElems = elems.view.mapValues(transform).toMap
      val recDefault = transform(default)
      bindIfCannotDuplicate(size, "sz") { sz =>
        t.Assert(
          t.GreaterEquals(sz, t.Int32Literal(0)),
          Some("Non-negative array size"),
          t.LargeArray(recElems, recDefault, sz, transform(base)).copiedFrom(e)
        ).copiedFrom(e)
      }

    case sel @ s.ADTSelector(recv, selector) =>
      if (sel.constructor.sort.constructors.size == 1)
        t.ADTSelector(transform(recv), selector).copiedFrom(e)
      else
        bindIfCannotDuplicate(recv, "recv") { recvx =>
          t.Assert(
            t.IsConstructor(recvx, sel.constructor.id).copiedFrom(e),
            Some("Cast error"),
            t.ADTSelector(recvx, selector).copiedFrom(e)
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

    // BigInt arithmetic compiled to uint32_t (--genc-bigint-as=uint32): the operations are
    // exact on BigInt, so a plain range check on the mathematical result is both necessary
    // and sufficient for the compiled C operation to be exact. Division and remainder need
    // no check: with both operands in [0, 2^32-1] (and the divisor nonzero, checked
    // unconditionally below), their results are always in range.
    case IntTyped(e0 @ s.Plus(lhs0, rhs0)) if bigIntCheck =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        assertInUInt32Range(t.Plus(lhsx, rhsx).copiedFrom(e), "Addition out of uint32 range", e)
      }}

    case IntTyped(e0 @ s.Minus(lhs0, rhs0)) if bigIntCheck =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        assertInUInt32Range(t.Minus(lhsx, rhsx).copiedFrom(e), "Subtraction out of uint32 range", e)
      }}

    case IntTyped(e0 @ s.Times(lhs0, rhs0)) if bigIntCheck =>
      bindIfCannotDuplicate(lhs0, "lhs") { lhsx =>
      bindIfCannotDuplicate(rhs0, "rhs") { rhsx =>
        assertInUInt32Range(t.Times(lhsx, rhsx).copiedFrom(e), "Multiplication out of uint32 range", e)
      }}

    case IntTyped(e0 @ s.UMinus(n0)) if bigIntCheck =>
      bindIfCannotDuplicate(n0, "inner") { innerx =>
        assertInUInt32Range(t.UMinus(innerx).copiedFrom(e), "Negation out of uint32 range", e)
      }

    // Bitvector to BigInt conversions must produce a value in [0, 2^32-1]; this holds by
    // construction for unsigned sources up to 32 bits, and needs a VC otherwise (signed
    // sources can be negative, 64-bit sources can exceed the range).
    case s.BVToInt(bv0) if bigIntCheck =>
      bv0.getType match {
        case s.BVType(false, size) if size <= 32 => super.transform(e)
        case _ =>
          bindIfCannotDuplicate(bv0, "bv") { x =>
            assertInUInt32Range(t.BVToInt(x).copiedFrom(e), "Bitvector to BigInt conversion out of uint32 range", e)
          }
      }

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

        d.getType match {
          case s.FPType(_, _) => rest
          case _ =>
            t.Assert(
              t.Not(t.Equals(dx, d.getType match {
                case s.IntegerType() => t.IntegerLiteral(0).copiedFrom(d)
                case s.BVType(signed, i) => t.BVLiteral(signed, 0, i).copiedFrom(d)
                case s.RealType() => t.FractionLiteral(0, 1).copiedFrom(d)
              }).copiedFrom(d)).copiedFrom(d),
              Some("Division by zero"),
              rest
            ).copiedFrom(e)
        }
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

    // Also injected in bigIntCheck mode: when BigInt is compiled to uint32_t, these bounds
    // are what makes the lowered narrowing cast exact, even with --strict-arithmetic=false.
    case s.IntToBV(size, signed, value) if checkOverflow || bigIntCheck =>
      bindIfCannotDuplicate(value, "i") { x =>      // x : IntegerType
        val (lo, hi) =
          if (signed) (-BigInt(2).pow(size - 1), BigInt(2).pow(size - 1) - 1)
          else        (BigInt(0),               BigInt(2).pow(size) - 1)
        t.Assert(
          t.GreaterEquals(x, t.IntegerLiteral(lo).copiedFrom(e)).copiedFrom(e),
          Some("BigInteger to bitvector conversion underflow"),
          t.Assert(
            t.LessEquals(x, t.IntegerLiteral(hi).copiedFrom(e)).copiedFrom(e),
            Some("BigInteger to bitvector conversion overflow"),
            t.IntToBV(size, signed, x).copiedFrom(e)
          ).copiedFrom(e)
        ).copiedFrom(e)
      }


    case s.FPToBVJVM(exponent, significand, toSize, expr) if checkOverflow =>
      bindIfCannotDuplicate(expr, "expr") { expr =>
        // a FP -> BV cast of the value `f` is considered safe iff `f` is not NaN and `bvLb < f < bvUb`.
        val bvLb = t.BVLiteral(true, -BigInt(2).pow(toSize-1) - 1, toSize + 1).copiedFrom(e)
        val bvUb = t.BVLiteral(true, BigInt(2).pow(toSize-1), toSize + 1).copiedFrom(e)
        t.Assert(
          t.Not(t.FPIsNaN(expr)).copiedFrom(e),
          Some("Safe floating-point to integer cast non-NaN check"),
          t.Assert( // For this assertion and the next one, we may assume that `expr` is not `NaN`.
            t.FPGreaterEquals(expr, t.FPCast(exponent, significand, t.RoundTowardNegative, bvLb)).copiedFrom(e),
            Some("Safe floating-point to integer cast lower bound"),
            t.Assert(
              t.FPLessEquals(expr, t.FPCast(exponent, significand, t.RoundTowardPositive, bvUb)).copiedFrom(e),
              Some("Safe floating-point to integer cast upper bound"),
              t.FPToBVJVM(exponent, significand, toSize, expr).copiedFrom(e)
            ).copiedFrom(e)
          ).copiedFrom(e)
        ).copiedFrom(e)
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

    case s.FPGreaterEquals(e1, e2) if checkOverflow => checkNaNBinop(e)(t.FPGreaterEquals.apply, e1, e2)
    case s.FPLessEquals(e1, e2) if checkOverflow => checkNaNBinop(e)(t.FPLessEquals.apply, e1, e2)
    case s.FPGreaterThan(e1, e2) if checkOverflow => checkNaNBinop(e)(t.FPGreaterThan.apply, e1, e2)
    case s.FPLessThan(e1, e2) if checkOverflow => checkNaNBinop(e)(t.FPLessThan.apply, e1, e2)
    case s.FPEquals(e1, e2) if checkOverflow => checkNaNBinop(e)(t.FPEquals.apply, e1, e2)

    // In bigIntCheck mode, spec conditions and ghost bindings are transformed with BigInt
    // bounds checks disabled: GenC never compiles them (all Assert/Assume/spec conditions
    // are discarded except exported preconditions, which the GenC lowering restricts to
    // arithmetic-free conditions). Other injected checks still apply within them.
    case s.Require(pre, body) if bigIntToUInt32 =>
      t.Require(inSpec(transform(pre)), transform(body)).copiedFrom(e)

    case s.Ensuring(body, pred) if bigIntToUInt32 =>
      t.Ensuring(transform(body), inSpec(transform(pred).asInstanceOf[t.Lambda])).copiedFrom(e)

    case s.Decreases(measure, body) if bigIntToUInt32 =>
      t.Decreases(inSpec(transform(measure)), transform(body)).copiedFrom(e)

    case s.Assert(cond, err, body) if bigIntToUInt32 =>
      t.Assert(inSpec(transform(cond)), err, transform(body)).copiedFrom(e)

    case s.Assume(cond, body) if bigIntToUInt32 =>
      t.Assume(inSpec(transform(cond)), transform(body)).copiedFrom(e)

    case s.Let(vd, value, body) if bigIntToUInt32 && (vd.flags contains s.Ghost) =>
      t.Let(transform(vd), inSpec(transform(value)), transform(body)).copiedFrom(e)

    case _ => super.transform(e)
  }

  private object BVTyped {
    def unapply(e: s.Expr): Option[(Boolean, Int, s.Expr)] = e.getType match {
      case s.BVType(signed, size) => Some((signed, size, e))
      case _ => None
    }
  }

  private object IntTyped {
    def unapply(e: s.Expr): Option[s.Expr] = e.getType match {
      case s.IntegerType() => Some(e)
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

  private def checkNaNBinop(e: s.Expr)(binop: (t.Expr, t.Expr) => t.Expr, e1: s.Expr, e2: s.Expr): t.Expr = {
    bindIfCannotDuplicate(e1, "e1") { e1x =>
      bindIfCannotDuplicate(e2, "e2") { e2x =>
        t.Assert(
          t.And(
            t.Not(t.FPIsNaN(e1x).copiedFrom(e)).copiedFrom(e),
            t.Not(t.FPIsNaN(e2x).copiedFrom(e)).copiedFrom(e)
          ).copiedFrom(e),
          Some("Comparison with NaN"),
          binop(e1x, e2x).copiedFrom(e)
        ).copiedFrom(e)
      }
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
      extends AssertionInjector(s, t,
        ctx.options.findOptionOrDefault(optStrictArithmetic),
        genc.bigIntToUInt32(ctx))
    val injector = new InjectorImpl(p.trees, p.trees)(using p.symbols)

    class TransformerImpl(override val s: p.trees.type, override val t: p.trees.type)
      extends inox.transformers.SymbolTransformer {
      import s._

      def transform(syms: Symbols): Symbols = {
        NoSymbols
          .withFunctions(syms.functions.values.toSeq.map { fd =>
            injector.wrapping(fd.flags.contains(s.Wrapping)) {
            injector.specOrGhost(fd.flags.contains(s.Ghost)) {
              new FunDef(
                fd.id,
                fd.tparams map injector.transform,
                fd.params map injector.transform,
                injector.transform(fd.returnType),
                injector.transform(fd.fullBody),
                fd.flags map injector.transform
              ).copiedFrom(fd)
            }}
          })
          .withSorts(syms.sorts.values.toSeq.map(injector.transform))
      }
    }

    new TransformerImpl(p.trees, p.trees)
  }
}
