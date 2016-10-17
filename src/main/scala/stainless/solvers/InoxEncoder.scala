/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

trait InoxEncoder extends inox.solvers.combinators.ProgramEncoder {
  val sourceProgram: Program
  val t: inox.trees.type = inox.trees

  val encoder: inox.ast.SymbolTransformer {
    val transformer: Encoder
  }

  val decoder: inox.ast.SymbolTransformer {
    val transformer: Decoder
  }

  trait Encoder extends inox.ast.TreeTransformer {
    val s: InoxEncoder.this.s.type = InoxEncoder.this.s
    val t: InoxEncoder.this.t.type = InoxEncoder.this.t

    object deconstructor extends {
      val s: Encoder.this.s.type = Encoder.this.s
      val t: Encoder.this.t.type = Encoder.this.t
    } with inox.ast.TreeDeconstructor

    import sourceProgram.symbols._

    override def transform(e: s.Expr): t.Expr = e match {
      case m: s.MatchExpr =>
        transform(matchToIfThenElse(m))

      case s.NoTree(_) =>
        throw inox.FatalError("Unexpected tree: " + e)

      case s.Error(tpe, desc) =>
        t.Variable(inox.ast.FreshIdentifier("error: " + desc, true), transform(tpe)).copiedFrom(e)

      case s.Require(pred, body) =>
        t.Assume(transform(pred), transform(body)).copiedFrom(e)

      case s.Ensuring(s.Require(pred, body), s.Lambda(Seq(res), post)) =>
        val vd = t.ValDef(res.id, transform(res.tpe))
        t.Assume(transform(pred),
          t.Let(vd, transform(body), t.Assume(transform(post), vd.toVariable)))

      case s.Ensuring(body, s.Lambda(Seq(res), post)) =>
        val vd = t.ValDef(res.id, transform(res.tpe))
        t.Let(vd, transform(body), t.Assume(transform(post), vd.toVariable))

      case s.Assert(pred, error, body) =>
        t.Assume(transform(pred), transform(body))

      case _ => super.transform(e)
    }
  }

  trait Decoder extends inox.ast.TreeTransformer {
    val s: InoxEncoder.this.t.type = InoxEncoder.this.t
    val t: InoxEncoder.this.s.type = InoxEncoder.this.s

    object deconstructor extends {
      val s: Decoder.this.s.type = Decoder.this.s
      val t: Decoder.this.t.type = Decoder.this.t
    } with inox.ast.TreeDeconstructor
  }
}

object InoxEncoder {
  def apply(p: StainlessProgram): InoxEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with InoxEncoder {
    object encoder extends inox.ast.SymbolTransformer {
      object transformer extends Encoder
    }

    object decoder extends inox.ast.SymbolTransformer {
      object transformer extends Decoder
    }
  }
}
