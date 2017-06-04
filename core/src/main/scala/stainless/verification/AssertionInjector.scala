/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait AssertionInjector extends ast.TreeTransformer {
  val s: ast.Trees
  val t: ast.Trees

  implicit val symbols: s.Symbols

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

    case s.AsInstanceOf(expr, ct) =>
      t.Assert(
        t.IsInstanceOf(transform(expr), transform(ct).asInstanceOf[t.ADTType]).copiedFrom(e),
        Some("Cast error"),
        super.transform(e)
      ).copiedFrom(e)

    case s.Division(_, d) =>
      t.Assert(
        t.Not(t.Equals(transform(d), d.getType match {
          case s.IntegerType => t.IntegerLiteral(0).copiedFrom(d)
          case s.BVType(i) => t.BVLiteral(0, i).copiedFrom(d)
          case s.RealType => t.FractionLiteral(0, 1).copiedFrom(d)
        }).copiedFrom(d)).copiedFrom(d),
        Some("Division by zero"),
        super.transform(e)
      ).copiedFrom(e)

    case s.Remainder(_, d) =>
      t.Assert(
        t.Not(t.Equals(transform(d), d.getType match {
          case s.IntegerType => t.IntegerLiteral(0).copiedFrom(d)
          case s.BVType(i) => t.BVLiteral(0, i).copiedFrom(d)
        }).copiedFrom(d)).copiedFrom(d),
        Some("Remainder by zero"),
        super.transform(e)
      ).copiedFrom(e)

    case s.Modulo(_, d) =>
      t.Assert(
        t.Not(t.Equals(transform(d), d.getType match {
          case s.IntegerType => t.IntegerLiteral(0).copiedFrom(d)
          case s.BVType(i) => t.BVLiteral(0, i).copiedFrom(d)
        }).copiedFrom(d)).copiedFrom(d),
        Some("Modulo by zero"),
        super.transform(e)
      ).copiedFrom(e)

    case _ => super.transform(e)
  }
}

object AssertionInjector {
  def apply(p: Program): inox.ast.SymbolTransformer {
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
      }

      t.NoSymbols
        .withFunctions(syms.functions.values.toSeq.map(injector.transform))
        .withADTs(syms.adts.values.toSeq.map(injector.transform))
    }
  }
}
