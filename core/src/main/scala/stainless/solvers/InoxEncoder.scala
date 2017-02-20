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
        .map(fd => fd.copy(flags = fd.flags.filter { case Derived(_) => false case _ => true }))
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

  protected val funIDs = (1 to maxArgs).map(i => i -> FreshIdentifier("fun" + i)).toMap
  protected val pres = (1 to maxArgs).map(i => i -> FreshIdentifier("pre")).toMap
  protected val fs   = (1 to maxArgs).map(i => i -> FreshIdentifier("f")).toMap

  protected val funADTs: Seq[t.ADTConstructor] = (1 to maxArgs).map { i =>
    val tparams @ (argTps :+ resTpe) = (1 to i).map {
      j => t.TypeParameter(FreshIdentifier("A" + j), Set(t.Variance(Some(false)))) // contravariant
    } :+ t.TypeParameter(FreshIdentifier("R"), Set(t.Variance(Some(true)))) // covariant

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

    import sourceProgram._
    import sourceProgram.symbols._

    override def transform(e: s.Expr): t.Expr = e match {
      case m: s.MatchExpr =>
        transform(matchToIfThenElse(m))

      case s.NoTree(tpe) =>
        throw new inox.FatalError("Unexpected empty tree: " + e)

      case s.Error(tpe, desc) =>
        t.Choose(
          t.ValDef(FreshIdentifier("error: " + desc, true), transform(tpe), Set.empty).copiedFrom(e),
          t.BooleanLiteral(true).copiedFrom(e)
        )

      case s.Require(pred, body) =>
        t.Assume(transform(pred), transform(body)).copiedFrom(e)

      case s.Ensuring(s.Require(pred, body), s.Lambda(Seq(res), post)) =>
        val vd = t.ValDef(res.id, transform(res.tpe), Set.empty)
        t.Assume(transform(pred),
          t.Let(vd, transform(body), t.Assume(transform(post), vd.toVariable)))

      case s.Ensuring(body, s.Lambda(Seq(res), post)) =>
        val vd = t.ValDef(res.id, transform(res.tpe), Set.empty)
        t.Let(vd, transform(body), t.Assume(transform(post), vd.toVariable))

      case s.Assert(pred, error, body) =>
        t.Assume(transform(pred), transform(body))

      case s.FiniteArray(elems, base) =>
        t.ADT(t.ADTType(arrayID, Seq(transform(base))), Seq(
          t.FiniteMap(
            elems.zipWithIndex.map { case (e, i) => t.IntLiteral(i) -> transform(e) },
            transform(simplestValue(base)),
            t.Int32Type,
            transform(base)),
          t.IntLiteral(elems.size)
        ))

      case s.LargeArray(elems, dflt, size, base) =>
        t.ADT(t.ADTType(arrayID, Seq(transform(dflt.getType))), Seq(
          t.FiniteMap(
            elems.toSeq.map(p => t.IntLiteral(p._1) -> transform(p._2)),
            transform(dflt),
            t.Int32Type,
            transform(base)),
          transform(size)
        ))

      case s.ArraySelect(array, index) =>
        t.MapApply(t.ADTSelector(transform(array), arr), transform(index))

      case s.ArrayUpdated(array, index, value) =>
        val na = transform(array)
        t.ADT(transform(array.getType).asInstanceOf[t.ADTType], Seq(
          t.MapUpdated(t.ADTSelector(na, arr), transform(index), transform(value)),
          t.ADTSelector(na, size)
        ))

      case s.ArrayLength(array) =>
        t.ADTSelector(transform(array), size)

      case s.Application(caller, args) => caller.getType match {
        case s.FunctionType(from, to) if from.nonEmpty =>
          t.Application(t.ADTSelector(transform(caller), fs(from.size)), args map transform)

        case _ => super.transform(e)
      }

      case s.Pre(f) => f.getType match {
        case s.FunctionType(from, to) if from.nonEmpty =>
          val tfrom = from map transform
          t.ADT(t.ADTType(funIDs(from.size), tfrom :+ t.BooleanType), Seq(
            t.ADTSelector(transform(f), pres(from.size)),
            t.Lambda(tfrom.map(tpe => t.ValDef(FreshIdentifier("x", true), tpe, Set.empty)), t.BooleanLiteral(true))
          ))

        case _ =>
          t.Lambda(Seq.empty, t.BooleanLiteral(true))
      }

      case s.Lambda(args, body) if args.nonEmpty =>
        val fArgs = args map transform
        val preArgs = args.map(vd => transform(vd.freshen))

        t.ADT(t.ADTType(funIDs(args.size), fArgs.map(_.tpe) :+ transform(body.getType)), Seq(
          super.transform(e),
          t.Lambda(preArgs, t.exprOps.replaceFromSymbols(
            (fArgs.map(_.toVariable) zip preArgs.map(_.toVariable)).toMap,
            transform(weakestPrecondition(body))
          ))
        ))

      case _ => super.transform(e)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ArrayType(base) =>
        t.ADTType(arrayID, Seq(transform(base)))
      case s.FunctionType(from, to) if from.nonEmpty =>
        t.ADTType(funIDs(from.size), from.map(transform) :+ transform(to))
      case _ => super.transform(tpe)
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
      *    Array(FiniteMap(pairs, _, _), IntLiteral(size))
      * }}}
      * where all keys in {{{pairs}}} are IntLiterals. This assumption also
      * holds on the output of [[SymbolsEncoder#TreeEncoder.transform(Expr)]].
      */
    override def transform(e: s.Expr): t.Expr = e match {
      case s.ADT(
        s.ADTType(`arrayID`, Seq(base)),
        Seq(s.FiniteMap(elems, dflt, _, _), s.IntLiteral(size))
      ) if size <= 10 =>
        val elemsMap = elems.toMap
        t.FiniteArray((0 until size).toSeq.map {
          i => transform(elemsMap.getOrElse(s.IntLiteral(i), dflt))
        }, transform(base))

      case s.ADT(s.ADTType(`arrayID`, Seq(base)), Seq(s.FiniteMap(elems, dflt, _, _), size)) =>
        t.LargeArray(
          elems.map { case (s.IntLiteral(i), e) => i -> transform(e) }.toMap,
          transform(dflt),
          transform(size),
          transform(base)
        )

      case s.ADT(s.ADTType(id, from :+ to), Seq(f, pre)) if funIDs.get(from.size) == Some(id) =>
        val s.Lambda(fArgs, fBody) = f
        val s.Lambda(preArgs, preBody) = pre

        val newPre = transform(s.exprOps.replaceFromSymbols(
          (preArgs.map(_.toVariable) zip fArgs.map(_.toVariable)).toMap,
          preBody
        ))

        def simplePre(pre: t.Expr): Boolean = {
          def rec(pre: t.Expr): Boolean = pre match {
            case t.IfExpr(cond, thenn, elze) if thenn == t.BooleanLiteral(true) => rec(elze)
            case t.BooleanLiteral(true) => true
            case _ => false
          }

          rec(sourceProgram.symbols.simplifyByConstructors(pre))
        }

        if (simplePre(newPre)) {
          transform(f)
        } else {
          t.Lambda(fArgs map transform, t.Require(newPre, transform(fBody)))
        }

      case _ => super.transform(e)
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.ADTType(`arrayID`, Seq(base)) =>
        t.ArrayType(transform(base))
      case s.ADTType(id, from :+ to) if funIDs.get(from.size) == Some(id) =>
        t.FunctionType(from map transform, transform(to))
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
