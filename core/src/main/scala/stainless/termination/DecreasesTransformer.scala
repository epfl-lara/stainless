/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

trait DecreasesTransformer extends transformers.TreeTransformer {
  val trees: ast.Trees

  val s: trees.type = trees
  val t: trees.type = trees

  implicit val symbols: trees.Symbols

  override def transform(e: s.Expr): t.Expr = e match {
    case s.Decreases(rank, body) =>
      val trank = transform(rank)
      val es = rank.getType match {
        case s.TupleType(tps) => tps.indices.map(i => t.TupleSelect(trank, i + 1))
        case _ => Seq(trank)
      }

      t.Assert(
        t.andJoin(es.map(e => t.GreaterEquals(e, e.getType match {
          case s.BVType(signed, size) => t.BVLiteral(signed, 0, size)
          case s.IntegerType() => t.IntegerLiteral(0)
          case tpe => throw inox.FatalError(s"Unexpected measure type ($tpe) for $e")
        }))),
        Some("Measure not guaranteed positive"),
        transform(body)
      ).copiedFrom(e)

    case _ => super.transform(e)
  }
}

object DecreasesTransformer {
  def apply(tr: ast.Trees)(syms: tr.Symbols): DecreasesTransformer {
    val trees: tr.type
  } = new {
    val trees: tr.type = tr
  } with DecreasesTransformer {
    implicit val symbols: syms.type = syms
  }
}
