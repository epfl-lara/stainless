/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

import inox.ast._

trait InoxEncoder extends ProgramEncoder {
  val sourceProgram: Program
  val t: inox.trees.type = inox.trees

  protected implicit val semantics: sourceProgram.Semantics

  override protected def encodedProgram: inox.Program { val trees: t.type } = {
    import sourceProgram.trees._
    import sourceProgram.symbols._

    inox.InoxProgram(sourceProgram.ctx, t.NoSymbols
      .withADTs(sourceProgram.symbols.adts.values.toSeq.map(encoder.transform))
      .withFunctions(sourceProgram.symbols.functions.values.toSeq
        .map(fd => fd.copy(flags = fd.flags.filter { case Derived(_) | Unchecked => false case _ => true }))
        .map { fd =>
          if (fd.flags contains Extern) {
            val Lambda(Seq(vd), post) = fd.postOrTrue
            encoder.transform(fd.copy(fullBody = fd.precondition match {
              case Some(pre) =>
                Require(pre, Choose(vd, post))

              case None =>
                Choose(vd, post)
            }, flags = fd.flags - Extern))
          } else {
            encoder.transform(fd)
          }
        }))
  }

  import t.dsl._

  protected val arrayID = FreshIdentifier("array")
  protected val arr  = FreshIdentifier("arr")
  protected val size = FreshIdentifier("size")

  protected val arrayInvariantID = FreshIdentifier("array_inv")
  protected val arrayInvariant = mkFunDef(arrayInvariantID)("A") { case Seq(aT) => (
    Seq("array" :: T(arrayID)(aT)), t.BooleanType, { case Seq(array) =>
      array.getField(size) >= E(0)
    })
  }

  protected val arrayADT: t.ADTConstructor = {
    val tdef = t.TypeParameterDef(t.TypeParameter.fresh("A"))
    new t.ADTConstructor(arrayID, Seq(tdef), None,
      Seq(t.ValDef(arr, t.MapType(t.Int32Type, tdef.tp), Set.empty), t.ValDef(size, t.Int32Type, Set.empty)),
      Set(t.HasADTInvariant(arrayInvariantID))
    )
  }

  protected val maxArgs = 10

  protected val funIDs = (0 to maxArgs).map(i => i -> FreshIdentifier("fun" + i)).toMap
  protected val pres = (0 to maxArgs).map(i => i -> FreshIdentifier("pre")).toMap
  protected val fs   = (0 to maxArgs).map(i => i -> FreshIdentifier("f")).toMap

  protected val funADTs: Seq[t.ADTConstructor] = (0 to maxArgs).map { i =>
    val tparams @ (argTps :+ resTpe) = (1 to i).map {
      j => t.TypeParameter(FreshIdentifier("A" + j), Set(t.Variance(false))) // contravariant
    } :+ t.TypeParameter(FreshIdentifier("R"), Set(t.Variance(true))) // covariant

    new t.ADTConstructor(
      funIDs(i),
      tparams.map(tp => t.TypeParameterDef(tp)),
      None,
      Seq(t.ValDef(fs(i), t.FunctionType(argTps, resTpe), Set.empty),
        t.ValDef(pres(i), t.FunctionType(argTps, t.BooleanType), Set.empty)),
      Set.empty
    )
  }

  protected override val extraFunctions: Seq[t.FunDef] = Seq(arrayInvariant)
  protected override val extraADTs: Seq[t.ADTDefinition] = arrayADT +: funADTs

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
          t.ValDef(FreshIdentifier("error: " + desc, true), transform(tpe), Set.empty).copiedFrom(e),
          t.BooleanLiteral(true).copiedFrom(e)
        ).copiedFrom(e)

      case s.Require(pred, body) =>
        transform(body)

      case s.Ensuring(s.Require(pred, body), s.Lambda(Seq(res), post)) =>
        val vd = transform(res)
        t.Assume(
          transform(pred),
          t.Let(vd, transform(body),
            t.Assume(transform(post), vd.toVariable).copiedFrom(e)).copiedFrom(e)
        ).copiedFrom(e)

      case s.Ensuring(body, s.Lambda(Seq(res), post)) =>
        val vd = transform(res)
        t.Let(vd, transform(body), t.Assume(transform(post), vd.toVariable).copiedFrom(e)).copiedFrom(e)

      case s.Assert(pred, error, body) =>
        t.Assume(transform(pred), transform(body)).copiedFrom(e)

      case s.FiniteArray(elems, base) =>
        t.ADT(t.ADTType(arrayID, Seq(transform(base))).copiedFrom(e), Seq(
          t.FiniteMap(
            elems.zipWithIndex.map { case (e, i) => t.Int32Literal(i).copiedFrom(e) -> transform(e) },
            transform(simplestValue(base).copiedFrom(e)),
            t.Int32Type,
            transform(base)),
          t.Int32Literal(elems.size).copiedFrom(e)
        ))

      case s.LargeArray(elems, dflt, size, base) =>
        t.ADT(t.ADTType(arrayID, Seq(transform(base))).copiedFrom(e), Seq(
          t.FiniteMap(
            elems.toSeq.map(p => t.Int32Literal(p._1).copiedFrom(e) -> transform(p._2)),
            transform(dflt),
            t.Int32Type,
            transform(base)),
          transform(size)
        )).copiedFrom(e)

      case s.ArraySelect(array, index) =>
        t.MapApply(t.ADTSelector(transform(array), arr).copiedFrom(e), transform(index)).copiedFrom(e)

      case s.ArrayUpdated(array, index, value) =>
        val na = transform(array)
        t.ADT(transform(array.getType).asInstanceOf[t.ADTType], Seq(
          t.MapUpdated(t.ADTSelector(na, arr).copiedFrom(e), transform(index), transform(value)).copiedFrom(e),
          t.ADTSelector(na, size).copiedFrom(e)
        )).copiedFrom(e)

      case s.ArrayLength(array) =>
        t.ADTSelector(transform(array), size).copiedFrom(e)

      case s.Application(caller, args) =>
        val s.FunctionType(from, to) = caller.getType
        t.Application(t.ADTSelector(transform(caller), fs(from.size)).copiedFrom(e), args map transform).copiedFrom(e)

      case s.Pre(f) =>
        val s.FunctionType(from, to) = f.getType
        val tfrom = from map transform
        t.ADT(t.ADTType(funIDs(from.size), tfrom :+ t.BooleanType).copiedFrom(e), Seq(
          t.ADTSelector(transform(f), pres(from.size)).copiedFrom(e),
          t.Lambda(
            tfrom.map(tpe => t.ValDef(FreshIdentifier("x", true), tpe, Set.empty).copiedFrom(tpe)),
            t.BooleanLiteral(true).copiedFrom(e)
          ).copiedFrom(e)
        )).copiedFrom(e)

      case s.Lambda(args, body) =>
        val fArgs = args map transform
        val preArgs = args.map(vd => transform(vd.freshen))

        t.ADT(t.ADTType(funIDs(args.size), fArgs.map(_.tpe) :+ transform(body.getType)).copiedFrom(e), Seq(
          body match {
            case s.Require(pred, body) => t.Lambda(args map transform, transform(body)).copiedFrom(body)
            case _ => super.transform(e)
          },
          t.Lambda(preArgs, t.exprOps.replaceFromSymbols(
            (fArgs.map(_.toVariable) zip preArgs.map(_.toVariable)).toMap,
            transform(weakestPrecondition(body))
          )).copiedFrom(e)
        ))

      case _ => super.transform(e)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ArrayType(base) =>
        t.ADTType(arrayID, Seq(transform(base))).copiedFrom(tpe)
      case s.FunctionType(from, to) =>
        t.ADTType(funIDs(from.size), from.map(transform) :+ transform(to)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }

    override def transform(vd: s.ValDef): t.ValDef = {
      super.transform(vd.copy(flags = vd.flags - s.Unchecked).copiedFrom(vd))
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
        s.ADTType(`arrayID`, Seq(base)),
        Seq(s.FiniteMap(elems, dflt, _, _), s.Int32Literal(size))
      ) if size <= 10 =>
        val elemsMap = elems.toMap
        t.FiniteArray((0 until size).toSeq.map {
          i => transform(elemsMap.getOrElse(s.Int32Literal(i).copiedFrom(e), dflt))
        }, transform(base)).copiedFrom(e)

      case s.ADT(s.ADTType(`arrayID`, Seq(base)), Seq(s.FiniteMap(elems, dflt, _, _), size)) =>
        t.LargeArray(
          elems.map { case (s.Int32Literal(i), e) => i -> transform(e) }.toMap,
          transform(dflt),
          transform(size),
          transform(base)
        ).copiedFrom(e)

      case s.ADT(s.ADTType(id, from :+ to), Seq(f, pre)) if funIDs.get(from.size) == Some(id) =>
        val s.Lambda(preArgs, preBody) = pre

        val simplePre: Boolean = {
          def rec(pre: s.Expr): Boolean = pre match {
            case s.IfExpr(cond, thenn, elze) if thenn == s.BooleanLiteral(true) => rec(elze)
            case s.BooleanLiteral(true) => true
            case _ => false
          }

          rec(targetProgram.symbols.simplifyByConstructors(preBody))
        }

        if (simplePre) {
          transform(f)
        } else {
          val (fArgs, fBody) = f match {
            case s.Lambda(fArgs, fBody) => (fArgs, fBody)
            case _ => // could be a choose!
              val fArgs = from.map(tpe => s.ValDef(FreshIdentifier("x", true), tpe).copiedFrom(tpe))
              val fBody = s.Application(f, fArgs.map(_.toVariable)).copiedFrom(f)
              (fArgs, fBody)
          }

          val newPre = transform(s.exprOps.replaceFromSymbols(
            (preArgs.map(_.toVariable) zip fArgs.map(_.toVariable)).toMap,
            preBody
          ).copiedFrom(preBody))

          t.Lambda(fArgs map transform, t.Require(newPre, transform(fBody)).copiedFrom(pre)).copiedFrom(e)
        }

      case _ => super.transform(e)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ADTType(`arrayID`, Seq(base)) =>
        t.ArrayType(transform(base)).copiedFrom(tpe)
      case s.ADTType(id, from :+ to) if funIDs.get(from.size) == Some(id) =>
        t.FunctionType(from map transform, transform(to)).copiedFrom(tpe)
      case _ => super.transform(tpe)
    }
  }
}

object InoxEncoder {
  def apply(p: StainlessProgram): InoxEncoder { val sourceProgram: p.type } = new {
    val sourceProgram: p.type = p
  } with InoxEncoder {
    val semantics = p.getSemantics
    object encoder extends TreeEncoder
    object decoder extends TreeDecoder
  }
}
