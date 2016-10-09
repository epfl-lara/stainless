/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

trait SolverEncoder {
  val program: Program { val trees: ast.Trees }
  import program._
  import program.trees._
  import program.symbols._

  val encoder: Encoder
  val decoder: Decoder

  lazy val targetProgram: Program { val trees: encoder.t.type } = program.transform(encoder)

  def encode(e: trees.Expr): inox.trees.Expr = encoder.transform(e)
  def encode(t: trees.Type): inox.trees.Type = encoder.transform(t)

  def decode(e: inox.trees.Expr): trees.Expr = decoder.transform(e)
  def decode(t: inox.trees.Type): trees.Type = decoder.transform(t)

  trait Encoder extends trees.TreeTransformer {
    val t: inox.trees.type = inox.trees

    override def transform(e: s.Expr): t.Expr = e match {
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

      case _ => super.transform(e)
    }
  }

  trait Decoder extends inox.trees.TreeTransformer {
    val t: trees.type = trees
  }
}

object SolverEncoder {
  def apply(p: StainlessProgram): SolverEncoder { val program: p.type } = new {
    val program: p.type = p
  } with SolverEncoder {
    object encoder extends Encoder {
      object deconstructor extends {
        val s: p.trees.type = p.trees
        val t: inox.trees.type = inox.trees
      } with ast.TreeDeconstructor
    }

    object decoder extends Decoder {
      object deconstructor extends {
        val s: inox.trees.type = inox.trees
        val t: p.trees.type = p.trees
      } with inox.ast.TreeDeconstructor
    }
  }
}
