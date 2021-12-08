/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package solvers

import inox.transformers._

class InoxEncoder private(override val t: inox.trees.type)
                         (override val sourceProgram: Program,
                          val context: inox.Context)
                         (encoder: TreeEncoder[sourceProgram.type],
                          decoder: TreeDecoder[sourceProgram.type])
                         (using protected val semantics: sourceProgram.Semantics)
  // `val s` is defined in ProgramEncoder as `sourceProgram.trees`, so we pass `sourceProgram.trees` where `s` is expected
  extends ProgramEncoder(t, sourceProgram, encoder, decoder)(
    encodedProgram = inox.InoxProgram(
      t.NoSymbols
        .withSorts(sourceProgram.symbols.sorts.values.toSeq
          .map(sort => sort.copy(flags = sort.flags.filter(keepFlag(sourceProgram))))
          .map(encoder.transform))
        .withFunctions(sourceProgram.symbols.functions.values.toSeq
          .map(fd => fd.copy(flags = fd.flags.filter(keepFlag(sourceProgram))))
          .map(encoder.transform))),
    extraFunctions = ArrayTheory.extraFunctions,
    extraSorts = ArrayTheory.extraSorts) {

  def this(sourceProgram: Program, context: inox.Context)
          (using semantics: sourceProgram.Semantics) =
    this(inox.trees)(sourceProgram, context)(
      new TreeEncoder[sourceProgram.type](sourceProgram)(using semantics, context),
      new TreeDecoder[sourceProgram.type](sourceProgram))
}

private object ArrayTheory {
  import inox.trees.dsl._
  val t: inox.trees.type = inox.trees

  val arrayID = FreshIdentifier("array")
  val arr  = FreshIdentifier("arr")
  val size = FreshIdentifier("size")

  val arrayInvariantID = FreshIdentifier("array_inv")
  val arrayInvariant = mkFunDef(arrayInvariantID)("A") { case Seq(aT) => (
    Seq("array" :: T(arrayID)(aT)), t.BooleanType(), { case Seq(array) =>
    array.getField(size) >= E(0)
  })
  }

  val arraySort: inox.trees.ADTSort = mkSort(arrayID, t.HasADTInvariant(arrayInvariantID))("A") {
    case Seq(aT) => Seq((
      arrayID.freshen,
      Seq(t.ValDef(arr, t.MapType(t.Int32Type(), aT)), t.ValDef(size, t.Int32Type()))
    ))
  }
  val Seq(arrayCons) = arraySort.constructors

  val maxArgs = 10

  val extraFunctions: Seq[t.FunDef] = Seq(arrayInvariant)
  val extraSorts: Seq[t.ADTSort] = Seq(arraySort)
}


private def keepFlag(sourceProgram: Program)(flag: sourceProgram.trees.Flag): Boolean = {
  import sourceProgram.trees._
  flag match {
    case DropVCs | DropConjunct | SplitVC | Library | Synthetic | PartialEval | Extern => false
    case Opaque | Private | Final | Law | Ghost | Erasable | Wrapping | Lazy => false
    case Derived(_) | IsField(_) | IsUnapply(_, _) | IndexedAt(_) | ClassParamInit(_) => false
    case TerminationStatus(_) => false
    case InlineInvariant | Template => false
    case _ => true
  }
}

private class TreeEncoder[Prog <: Program](val sourceProgram: Prog)
                                          (override val s: sourceProgram.trees.type,
                                           override val t: inox.trees.type)
                                          (using val semantics: sourceProgram.Semantics,
                                           val context: inox.Context)
  extends TreeTransformer {
  import ArrayTheory.{t => _, _}
  import s._
  import sourceProgram._
  import sourceProgram.symbols.{given, _}
  import t.dsl._

  def this(sourceProgram: Prog)(using semantics: sourceProgram.Semantics, context: inox.Context) =
    this(sourceProgram)(sourceProgram.trees, inox.trees)

  override def transform(e: s.Expr): t.Expr = {
    e match {
      case m: s.MatchExpr =>
        transform(matchToIfThenElse(m))

      case p: s.Passes =>
        transform(matchToIfThenElse(p.asConstraint))

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

      case s.Decreases(measure, body) =>
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

      case s.SizedADT(sort, tps, args, size) => transform(s.ADT(sort, tps, args))

      case m: s.Max =>
        transform(maxToIfThenElse(m))

      case _ => super.transform(e)
    }
  }

  override def transform(tpe: s.Type): t.Type = tpe match {
    case s.ArrayType(base) =>
      t.ADTType(arrayID, Seq(transform(base))).copiedFrom(tpe)

    case s.RecursiveType(sort, tps, size) => transform(s.ADTType(sort, tps))

    case s.ValueType(tpe) => transform(tpe)

    case s.AnnotatedType(tpe, _) => transform(tpe)

    case _ => super.transform(tpe)
  }

  override def transform(vd: s.ValDef): t.ValDef = {
    super.transform(vd.copy(flags = vd.flags.filter(keepFlag(sourceProgram))).copiedFrom(vd))
  }
}

private class TreeDecoder[Prog <: Program](val sourceProgram: Prog)
                                          (override val s: inox.trees.type,
                                           override val t: sourceProgram.trees.type)
  extends TreeTransformer {

  import ArrayTheory.{t => _, _}

  def this(sourceProgram: Prog) = this(sourceProgram)(inox.trees, sourceProgram.trees)

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

object InoxEncoder {
  def apply(p: StainlessProgram, ctx: inox.Context): InoxEncoder { val sourceProgram: p.type } = {
    class Impl(override val sourceProgram: p.type) extends InoxEncoder(sourceProgram, ctx)(using p.getSemantics)
    new Impl(p)
  }
}
