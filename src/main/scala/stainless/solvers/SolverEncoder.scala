/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

trait SolverEncoder {
  val trees: ast.Trees

  val encoder: Encoder
  val decoder: Decoder

  def encode(e: trees.Expr)(implicit s: trees.Symbols): inox.trees.Expr = encoder.transform(e)
  def encode(t: trees.Type): inox.trees.Type = encoder.translate(t)

  def decode(e: inox.trees.Expr): trees.Expr = decoder.translate(e)
  def decode(t: inox.trees.Type): trees.Type = decoder.translate(t)

  trait Encoder extends inox.ast.TreeDeconstructor {
    protected val s: trees.type = trees
    protected val t: inox.trees.type = inox.trees

    def transform(e: s.Expr)(implicit syms: s.Symbols): t.Expr = e match {
      case m: s.MatchExpr =>
        transform(syms.matchToIfThenElse(m))

      case s.NoTree(_) =>
        throw inox.FatalError("Unexpected tree: " + e)

      case s.Error(tpe, desc) =>
        t.Variable(inox.ast.FreshIdentifier("error: " + desc, true), translate(tpe)).copiedFrom(e)

      case s.Require(pred, body) =>
        t.Assume(transform(pred), transform(body)).copiedFrom(e)

      case s.Ensuring(s.Require(pred, body), s.Lambda(Seq(res), post)) =>
        val vd = t.ValDef(res.id, translate(res.tpe))
        t.Assume(transform(pred),
          t.Let(vd, transform(body), t.Assume(transform(post), vd.toVariable)))

      case s.Ensuring(body, s.Lambda(Seq(res), post)) =>
        val vd = t.ValDef(res.id, translate(res.tpe))
        t.Let(vd, transform(body), t.Assume(transform(post), vd.toVariable))

      case s.Assert(pred, error, body) =>
        t.Assume(transform(pred), transform(body))

      case _ =>
        val (es, tps, recons) = deconstruct(e)
        recons(es map transform, tps map translate)
    }
  }

  trait Decoder extends inox.ast.TreeDeconstructor {
    protected val s: inox.trees.type = inox.trees
    protected val t: trees.type = trees
  }
}
