/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package solvers

import inox.transformers._

trait InoxEncoder extends ProgramEncoder {
  val sourceProgram: Program
  val context: inox.Context
  val t: inox.trees.type = inox.trees

  import sourceProgram.trees._
  import sourceProgram.symbols._

  protected implicit val semantics: Semantics

  import context._

  private[this] def keepFlag(flag: Flag): Boolean = flag match {
    case Unchecked | Synthetic | PartialEval | Extern | Opaque | Private | Final | Ghost => false
    case Derived(_) | IsField(_) | IsUnapply(_, _) => false
    case _ => true
  }

  override protected def encodedProgram: inox.Program { val trees: t.type } = {
    inox.InoxProgram(t.NoSymbols
      .withSorts(sourceProgram.symbols.sorts.values.toSeq
        .map(sort => sort.copy(flags = sort.flags.filter(keepFlag)))
        .map(encoder.transform))
      .withFunctions(sourceProgram.symbols.functions.values.toSeq
        .map(fd => fd.copy(flags = fd.flags.filter(keepFlag)))
        .map(encoder.transform)))
  }

  import t.dsl._

  protected val arrayID = FreshIdentifier("array")
  protected val arr  = FreshIdentifier("arr")
  protected val size = FreshIdentifier("size")

  protected val arrayInvariantID = FreshIdentifier("array_inv")
  protected val arrayInvariant = mkFunDef(arrayInvariantID)("A") { case Seq(aT) => (
    Seq("array" :: T(arrayID)(aT)), t.BooleanType(), { case Seq(array) =>
      array.getField(size) >= E(0)
    })
  }

  protected val arraySort: t.ADTSort = mkSort(arrayID, t.HasADTInvariant(arrayInvariantID))("A") {
    case Seq(aT) => Seq((
      arrayID.freshen,
      Seq(t.ValDef(arr, t.MapType(t.Int32Type(), aT)), t.ValDef(size, t.Int32Type()))
    ))
  }
  protected val Seq(arrayCons) = arraySort.constructors

  protected val maxArgs = 10

  protected override val extraFunctions: Seq[t.FunDef] = Seq(arrayInvariant)
  protected override val extraSorts: Seq[t.ADTSort] = Seq(arraySort)

  val encoder: TreeEncoder
  val decoder: TreeDecoder

  protected class TreeEncoder extends TreeTransformer {
    val s: InoxEncoder.this.s.type = InoxEncoder.this.s
    val t: InoxEncoder.this.t.type = InoxEncoder.this.t

    import s._
    import sourceProgram._
    import sourceProgram.symbols._

    override def transform(e: s.Expr): t.Expr = e match {
      case m: s.MatchExpr =>
        transform(matchToIfThenElse(m))

      case s.NoTree(tpe) =>
        t.Choose(
          t.ValDef(FreshIdentifier("empty", true), transform(tpe)).copiedFrom(e),
          t.BooleanLiteral(true).copiedFrom(e)
        ).copiedFrom(e)

      case s.Error(tpe, desc) =>
        t.Choose(
          t.ValDef(FreshIdentifier("error: " + desc, true), transform(tpe)).copiedFrom(e),
          t.BooleanLiteral(true).copiedFrom(e)
        ).copiedFrom(e)

      case s.Require(pred, body) =>
        transform(body)

      case s.Ensuring(s.Require(pred, body), s.Lambda(Seq(res), post)) =>
        val vd = transform(res)
        val postWithAssumes = s.exprOps.postMap {
          case as @ s.Assert(pred, _, body) => Some(s.Assume(pred, body).copiedFrom(as))
          case _ => None
        } (post)

        t.Assume(
          transform(pred),
          t.Let(vd, transform(body),
            t.Assume(transform(postWithAssumes), vd.toVariable).copiedFrom(e)).copiedFrom(e)
        ).copiedFrom(e)

      case s.Ensuring(body, s.Lambda(Seq(res), post)) =>
        val vd = transform(res)
        val postWithAssumes = s.exprOps.postMap {
          case as @ s.Assert(pred, _, body) => Some(s.Assume(pred, body).copiedFrom(as))
          case _ => None
        } (post)

        t.Let(vd, transform(body), t.Assume(transform(postWithAssumes), vd.toVariable).copiedFrom(e)).copiedFrom(e)

      case s.Assert(pred, error, body) =>
        transform(body)

      case s.Annotated(body, _) => transform(body)

      case s.FiniteArray(elems, base) =>
        t.ADT(arrayCons.id, Seq(transform(base)), Seq(
          t.FiniteMap(
            elems.zipWithIndex.map { case (e, i) => t.Int32Literal(i).copiedFrom(e) -> transform(e) },
            if (hasInstance(base) contains true) transform(simplestValue(base)).copiedFrom(e)
            else if (elems.nonEmpty) transform(elems.head)
            else t.Choose(
              t.ValDef(FreshIdentifier("res"), transform(base)).copiedFrom(e),
              t.BooleanLiteral(true).copiedFrom(e)
            ).copiedFrom(e),
            t.Int32Type(),
            transform(base)),
          t.Int32Literal(elems.size).copiedFrom(e)
        ))

      case s.LargeArray(elems, dflt, size, base) =>
        t.ADT(arrayCons.id, Seq(transform(base)), Seq(
          t.FiniteMap(
            elems.toSeq.map(p => t.Int32Literal(p._1).copiedFrom(e) -> transform(p._2)),
            transform(dflt),
            t.Int32Type(),
            transform(base)),
          transform(size)
        )).copiedFrom(e)

      case s.ArraySelect(array, index) =>
        t.MapApply(t.ADTSelector(transform(array), arr).copiedFrom(e), transform(index)).copiedFrom(e)

      case s.ArrayUpdated(array, index, value) =>
        val na = transform(array)
        val t.ADTType(_, tps) = transform(array.getType)
        t.ADT(arrayCons.id, tps, Seq(
          t.MapUpdated(t.ADTSelector(na, arr).copiedFrom(e), transform(index), transform(value)).copiedFrom(e),
          t.ADTSelector(na, size).copiedFrom(e)
        )).copiedFrom(e)

      case s.ArrayLength(array) =>
        t.ADTSelector(transform(array), size).copiedFrom(e)

      case s.Application(caller, args) =>
        val s.FunctionType(from, to) = caller.getType
        t.Application(transform(caller).copiedFrom(e), args map transform).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ArrayType(base) =>
        t.ADTType(arrayID, Seq(transform(base))).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }

    override def transform(vd: s.ValDef): t.ValDef = {
      super.transform(vd.copy(flags = vd.flags.filter(keepFlag)).copiedFrom(vd))
    }
  }

  protected class TreeDecoder extends TreeTransformer {
    val s: InoxEncoder.this.t.type = InoxEncoder.this.t
    val t: InoxEncoder.this.s.type = InoxEncoder.this.s

    /** Transform back from encoded array ADTs into stainless arrays.
      * Note that this translation should only occur on models returned by
      * the Inox solver, so we can assume that the array adts have the
      * shape:
      * {{{
      *    Array(FiniteMap(pairs, _, _), Int32Literal(size))
      * }}}
      * where all keys in {{{pairs}}} are Int32Literals. This assumption also
      * holds on the output of [[SymbolsEncoder#TreeEncoder.transform(Expr)]].
      */
    override def transform(e: s.Expr): t.Expr = e match {
      case s.ADT(
        arrayCons.id,
        Seq(base),
        Seq(s.FiniteMap(elems, dflt, _, _), s.Int32Literal(size))
      ) if size <= 10 =>
        val elemsMap = elems.toMap
        t.FiniteArray((0 until size).map {
          i => transform(elemsMap.getOrElse(s.Int32Literal(i).copiedFrom(e), dflt))
        }, transform(base)).copiedFrom(e)

      case s.ADT(arrayCons.id, Seq(base), Seq(s.FiniteMap(elems, dflt, _, _), size)) =>
        t.LargeArray(
          elems.map { case (s.Int32Literal(i), e) => i -> transform(e) }.toMap,
          transform(dflt),
          transform(size),
          transform(base)
        ).copiedFrom(e)

      case _ => super.transform(e)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ADTType(`arrayID`, Seq(base)) =>
        t.ArrayType(transform(base)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }
}

object InoxEncoder {
  def apply(p: StainlessProgram, ctx: inox.Context): InoxEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
    val context = ctx
  } with InoxEncoder {
    val semantics = p.getSemantics
    object encoder extends TreeEncoder
    object decoder extends TreeDecoder
  }
}
