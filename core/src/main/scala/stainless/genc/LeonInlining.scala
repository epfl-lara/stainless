/* Copyright 2009-2021 EPFL, Lausanne */

/* Copy of FunctionInlining.scala with Classes/TypeDefs with a few modifications */

package stainless
package genc

import extraction._

class LeonInlining(override val s: oo.Trees, override val t: oo.Trees)(using override val context: inox.Context)
  extends CachingPhase
     with extraction.IdentitySorts
     with oo.IdentityClasses
     with oo.IdentityTypeDefs { self =>
  import s._

  // The function inlining transformation depends on all (transitive) callees
  // that will require inlining.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({(fd, symbols) =>
    FunctionKey(fd) + SetKey(
      symbols.dependencies(fd.id)
        .flatMap(id => symbols.lookupFunction(id))
        .filter(_.flags exists { _.name == "cCode.inlining" })
    )
  })

  override protected type FunctionResult = Option[t.FunDef]
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private[this] class Identity(override val s: self.s.type, override val t: self.t.type) extends transformers.ConcreteTreeTransformer(s, t)
  private[this] val identity = new Identity(self.s, self.t)

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(syms: s.Symbols, fd: s.FunDef): Option[t.FunDef] = {
    import syms.{given, _}

    object Inliner extends s.ConcreteOOSelfTreeTransformer { inlSelf =>

      override def transform(expr: inlSelf.s.Expr): inlSelf.t.Expr = expr match {
        case fi: FunctionInvocation =>
          inlineFunctionInvocations(fi.copy(args = fi.args map transform).copiedFrom(fi)).copiedFrom(fi)

        case _ => super.transform(expr)
      }

      // values that can be inlined directly, without being let-bound
      private def isValue(e: Expr): Boolean = e match {
        case _: Variable => true
        case UnitLiteral() => true
        case BooleanLiteral(_) => true
        case IntegerLiteral(_) => true
        case BVLiteral(_, _, _) => true
        case ClassSelector(obj, id) if isValue(obj) =>
          val ct = obj.getType
          if (ct.isInstanceOf[ClassType]) {
            val cd = ct.asInstanceOf[ClassType].tcd.cd
            cd.parents.isEmpty && cd.children.isEmpty
          } else
            false
        case Tuple(es) => es.forall(isValue)
        case FiniteArray(args, base) => args.forall(isValue)
        case LargeArray(elems, default, _, _) => elems.map(_._2).forall(isValue) && isValue(default)
        case ADT(_, _, args) => args.forall(isValue)
        case _ => false
      }

      private def inlineFunctionInvocations(fi: FunctionInvocation): Expr = {
        import exprOps._
        val (tfd, args) = (fi.tfd, fi.args)

        val isGhost = tfd.fd.flags contains Ghost
        val isSynthetic = tfd.fd.flags contains Synthetic
        val hasInlineFlag = tfd.fd.flags contains Inline
        val hasCInlineFlag = tfd.fd.flags.exists(_.name == "cCode.inline")

        def willInline = hasCInlineFlag || (hasInlineFlag && isSynthetic)

        if (!willInline) return fi

        val specced = BodyWithSpecs(tfd.fullBody)
        // simple path for inlining when all arguments are values, and the function's
        // body doesn't contain other function invocations.

        if (args.forall(isValue)) {
          transform(exprOps.replaceFromSymbols(tfd.params.zip(args).toMap, exprOps.freshenLocals(specced.letsAndBody)))
        } else {
          // We need to keep the body as-is for `@synthetic` methods, such as
          // `copy` or implicit conversions for implicit classes, in order to
          // later on check that the class invariant is valid.
          val body = specced.bodyOpt match {
            case Some(body) => body
            case _ => NoTree(tfd.returnType).copiedFrom(tfd.fullBody)
          }

          val result = (tfd.params zip args).foldRight(specced.wrapLets(body)) {
            case ((vd, e), body) => let(vd, e, body).setPos(fi)
          }

          val freshened = exprOps.freshenLocals(result)

          transform(freshened)
        }
      }
    }

    if ((fd.flags contains Synthetic) && (fd.flags contains Inline) && (!fd.flags.exists(_.isInstanceOf[ClassParamInit]))) None
    else Some(identity.transform(fd.copy(
      fullBody = Inliner.transform(fd.fullBody),
      flags = fd.flags filterNot (f => f == Inline || f == InlineOnce || f.name == "cCode.inline")
    )))
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val newSymbols = super.extractSymbols(context, symbols)

    t.NoSymbols
      .withSorts(newSymbols.sorts.values.toSeq)
      .withClasses(newSymbols.classes.values.toSeq)
      .withTypeDefs(newSymbols.typeDefs.values.toSeq)
      .withFunctions(newSymbols.functions.values.toSeq)
  }
}

object LeonInlining {
  def apply(ts: oo.Trees, tt: oo.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type)(using override val context: inox.Context) extends LeonInlining(s, t)
    new Impl(ts, tt)
  }
}
