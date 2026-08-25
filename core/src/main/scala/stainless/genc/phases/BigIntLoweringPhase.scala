/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import extraction._
import extraction.throwing.{ trees => tt }

/**
 * Lower `BigInt` (IntegerType) to 32-bit unsigned bitvectors, so that downstream phases
 * compile it to C `uint32_t` (enabled by `--genc-bigint-as=uint32`).
 *
 * This mapping is only sound for programs verified with the same option: verification
 * then proves that every BigInt value stays within [0, 2^32-1] (see
 * [[stainless.verification.AssertionInjector]]), so by induction every runtime uint32
 * value equals the BigInt value of the source semantics. On non-negative operands, C's
 * `/` and `%` coincide with the BigInt Division/Remainder semantics, and `mod` coincides
 * with `%`, so `mod` is lowered to `%`.
 *
 * Preconditions of exported functions are compiled to *runtime* checks against
 * unverified C callers, so no VC can bound arithmetic inside them; BigInt arithmetic is
 * therefore rejected there (comparisons between already-computed values are exact and
 * remain allowed). This phase runs after [[GhostEliminationPhase]], so ghost BigInt code
 * is already gone and preconditions of exported functions have been folded into
 * `Assert(cond, Some("Dynamic precondition check"), _)`.
 */
class BigIntLowering(override val s: tt.type,
                     override val t: throwing.Trees)
                    (val symbols: tt.Symbols,
                     val context: inox.Context) extends inox.transformers.Transformer {

  case class Env()

  private val uint32Max = BigInt(2).pow(32) - 1

  private def uint32 = t.BVType(false, 32)

  override def transform(tpe: s.Type, env: Env): t.Type = tpe match {
    case s.IntegerType() => t.BVType(false, 32).copiedFrom(tpe)
    case _ => super.transform(tpe, env)
  }

  override def transform(expr: s.Expr, env: Env): t.Expr = expr match {
    case s.IntegerLiteral(v) =>
      if (v < 0 || v > uint32Max)
        context.reporter.fatalError(expr.getPos,
          s"BigInt literal $v does not fit in uint32_t (required by --genc-bigint-as=uint32)")
      t.BVLiteral(false, v, 32).copiedFrom(expr)

    // BV -> BigInt conversions; exact thanks to the [0, 2^32-1] VCs injected by
    // verification under --genc-bigint-as=uint32 (unsigned sources up to 32 bits
    // are in range by construction).
    case s.BVToInt(e) => e.getType(using symbols) match {
      case s.BVType(false, 32) =>
        transform(e, env)
      case s.BVType(false, size) if size < 32 =>
        t.BVWideningCast(transform(e, env), uint32.copiedFrom(expr)).copiedFrom(expr)
      case s.BVType(false, 64) =>
        t.BVNarrowingCast(transform(e, env), uint32.copiedFrom(expr)).copiedFrom(expr)
      case s.BVType(true, 32) =>
        t.BVSignedToUnsigned(transform(e, env)).copiedFrom(expr)
      case s.BVType(true, size) if size < 32 =>
        t.BVSignedToUnsigned(
          t.BVWideningCast(transform(e, env), t.BVType(true, 32).copiedFrom(expr)).copiedFrom(expr)
        ).copiedFrom(expr)
      case s.BVType(true, 64) =>
        // value in [0, 2^32-1]: go through uint64 (a direct narrowing to int32 could not
        // represent values above 2^31 - 1)
        t.BVNarrowingCast(
          t.BVSignedToUnsigned(transform(e, env)).copiedFrom(expr),
          uint32.copiedFrom(expr)
        ).copiedFrom(expr)
      case tpe =>
        context.reporter.fatalError(expr.getPos, s"Unexpected BigInt conversion from type ${tpe.asString(using s.PrinterOptions.fromContext(context))}")
    }

    // BigInt -> BV conversions; exact thanks to the target-range VCs injected by
    // verification under --genc-bigint-as=uint32.
    case s.IntToBV(size, signed, e) =>
      val e32 = transform(e, env)
      (signed, size) match {
        case (false, 32) => e32
        case (false, sz) if sz < 32 =>
          t.BVNarrowingCast(e32, t.BVType(false, sz).copiedFrom(expr)).copiedFrom(expr)
        case (false, 64) =>
          t.BVWideningCast(e32, t.BVType(false, 64).copiedFrom(expr)).copiedFrom(expr)
        case (true, 32) =>
          t.BVUnsignedToSigned(e32).copiedFrom(expr)
        case (true, sz) if sz < 32 =>
          t.BVUnsignedToSigned(
            t.BVNarrowingCast(e32, t.BVType(false, sz).copiedFrom(expr)).copiedFrom(expr)
          ).copiedFrom(expr)
        case (true, 64) =>
          t.BVUnsignedToSigned(
            t.BVWideningCast(e32, t.BVType(false, 64).copiedFrom(expr)).copiedFrom(expr)
          ).copiedFrom(expr)
        case _ =>
          context.reporter.fatalError(expr.getPos, s"Unsupported BigInt conversion to a $size-bit bitvector")
      }

    // On non-negative operands, mod coincides with % (both operands are in
    // [0, 2^32-1] by the verified invariant).
    case s.Modulo(a, b) if expr.getType(using symbols) == s.IntegerType() =>
      t.Remainder(transform(a, env), transform(b, env)).copiedFrom(expr)

    case s.StringLength(_) | s.SubString(_, _, _) =>
      context.reporter.fatalError(expr.getPos,
        "String operations returning or taking BigInt are not supported with --genc-bigint-as=uint32")

    // Preconditions of exported functions run as unverified C-side checks: no VC can
    // bound their arithmetic, so only arithmetic-free conditions are allowed.
    case s.Assert(cond, Some("Dynamic precondition check"), _) =>
      checkExportedPreconditionArithmeticFree(cond)
      super.transform(expr, env)

    case _ => super.transform(expr, env)
  }

  private def checkExportedPreconditionArithmeticFree(cond: s.Expr): Unit = {
    import s._
    exprOps.preTraversal {
      case e @ (Plus(_, _) | Minus(_, _) | Times(_, _) | UMinus(_) | Division(_, _) | Remainder(_, _) | Modulo(_, _))
          if e.getType(using symbols) == IntegerType() =>
        context.reporter.fatalError(e.getPos,
          "BigInt arithmetic is not allowed in preconditions of exported functions with " +
          "--genc-bigint-as=uint32: the check runs at runtime on unverified C inputs, where " +
          "the arithmetic itself could overflow. Only comparisons are allowed here.")
      case _ => ()
    }(cond)
  }

  def transform(cd: s.ClassDef, env: Env): t.ClassDef = {
    new t.ClassDef(
      cd.id,
      cd.tparams.map(transform(_, env)),
      cd.parents.map(transform(_, env)).map(_.asInstanceOf[t.ClassType]),
      cd.fields.map(transform(_, env)),
      cd.flags.map(transform(_, env))
    ).setPos(cd)
  }

  def transform(cons: s.ADTConstructor, env: Env): t.ADTConstructor = {
    new t.ADTConstructor(
      cons.id,
      cons.sort,
      cons.fields.map(transform(_, env))
    ).setPos(cons)
  }

  def transform(sort: s.ADTSort, env: Env): t.ADTSort = {
    new t.ADTSort(
      sort.id,
      sort.tparams.map(transform(_, env)),
      sort.constructors.map(transform(_, env)),
      sort.flags.map(transform(_, env))
    ).setPos(sort)
  }

  def transform(fd: s.FunDef, env: Env): t.FunDef = {
    new t.FunDef(
      fd.id,
      fd.tparams.map(transform(_, env)),
      fd.params.map(transform(_, env)),
      transform(fd.returnType, env),
      transform(fd.fullBody, env),
      fd.flags.map(transform(_, env))
    ).setPos(fd)
  }

  def transform(symbols: s.Symbols): t.Symbols = {
    val emptyEnv = Env()
    t.NoSymbols
      .withFunctions(symbols.functions.values.toSeq.map(transform(_, emptyEnv)))
      .withSorts(symbols.sorts.values.toSeq.map(transform(_, emptyEnv)))
      .withClasses(symbols.classes.values.toSeq.map(transform(_, emptyEnv)))
  }

}

class BigIntLoweringPhase(using override val context: inox.Context) extends LeonPipeline[tt.Symbols, tt.Symbols](context) {
  val name = "BigInt Lowering"

  given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  def run(syms: tt.Symbols): tt.Symbols = {
    if (!bigIntToUInt32(context)) syms // when disabled, BigInt is rejected later by Scala2IRPhase
    else {
      class Impl(override val s: tt.type, override val t: tt.type)
        extends BigIntLowering(s, t)(syms, context)
      new Impl(tt, tt).transform(syms)
    }
  }
}
