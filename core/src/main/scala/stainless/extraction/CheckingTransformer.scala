/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

case class CheckFailedError(msg: String) extends Exception(s"Lowering failed on $msg")

trait CheckingTransformer extends transformers.TreeTransformer {

  override def transform(id: Identifier, tpe: s.Type): (Identifier, t.Type) = try {
    super.transform(id, tpe)
  } catch {
    case _: MatchError => throw CheckFailedError(s"($id,$tpe)")
  }

  override def transform(vd: s.ValDef): t.ValDef = try {
    super.transform(vd)
  } catch {
    case _: MatchError => throw CheckFailedError(s"$vd")
  }

  override def transform(e: s.Expr): t.Expr = try {
    super.transform(e)
  } catch {
    case _: MatchError => throw CheckFailedError(s"$e")
  }

  override def transform(tpe: s.Type): t.Type = try {
    super.transform(tpe)
  } catch {
    case _: MatchError => throw CheckFailedError(s"$tpe")
  }

  override def transform(pat: s.Pattern): t.Pattern = try {
    super.transform(pat)
  } catch {
    case _: MatchError => throw CheckFailedError(s"$pat")
  }
}
