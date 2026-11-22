/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

class FieldAccessors(override val s: Trees, override val t: oo.Trees)
                    (using override val context: inox.Context)
  extends oo.CachingPhase
     with oo.NoSummaryPhase
     with SimpleSorts
     with oo.SimpleClasses
     with SimplyCachedSorts
     with oo.IdentityTypeDefs { self =>

  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(self.s, self.t, symbols)

  protected class TransformerContext(override val s: self.s.type,
                                     override val t: self.t.type,
                                     val symbols: s.Symbols,
                                     inFieldTypes: Boolean = false)
    extends oo.ConcreteTreeTransformer(s, t) {
    import symbols.{given, _}

    def isConcreteAccessor(fd: FunDef): Boolean = fd.isAccessor && !fd.isAbstract && !fd.body.isEmpty

    /** Whether `fd` is an accessor that dispatches to the accessors that override it, as lifted by
      * `MethodLifting` (after `Sealing`, every concrete class of the hierarchy reads a field).
      */
    def isAccessorDispatcher(fd: FunDef): Boolean =
      fd.isAccessor && fd.isAbstract && fd.body.exists(!_.isInstanceOf[NoTree])

    /** Field types can't call functions over their own sort, so the accessors in field types are inlined
      * together with their dispatchers, as in the refinements of the fields of member classes, such as
      * `List[{ x: C | x.outer eq $outer }]` (see `xlang.MemberClasses`).
      */
    def isInlined(fd: FunDef): Boolean = isConcreteAccessor(fd) || (inFieldTypes && isAccessorDispatcher(fd))

    lazy val inFieldTypesContext: TransformerContext =
      if (inFieldTypes) this else new TransformerContext(s, t, symbols, inFieldTypes = true)

    /** The accessors and dispatchers that are inlined in the field types of `cd`. */
    def fieldTypeInlinings(cd: ClassDef): Set[Identifier] = {
      val ctx = inFieldTypesContext
      def rec(seen: Set[Identifier], todo: Seq[Identifier]): Set[Identifier] = todo match {
        case Seq() => seen
        case id +: rest =>
          val fd = symbols.getFunction(id)
          val next = s.exprOps.functionCallsOf(fd.fullBody).map(_.id).filterNot(seen)
            .filter(fid => ctx.isInlined(symbols.getFunction(fid)))
          rec(seen ++ next, rest ++ next)
      }
      val roots = cd.fields.flatMap(vd => s.typeOps.collect[Identifier] {
        case s.RefinementType(_, pred) => s.exprOps.functionCallsOf(pred).map(_.id)
        case _ => Set.empty[Identifier]
      } (vd.tpe)).toSet.filter(fid => ctx.isInlined(symbols.getFunction(fid)))
      rec(roots, roots.toSeq)
    }

    override def transform(e: s.Expr): t.Expr = e match {
      case FunctionInvocation(id, tps, args) if isInlined(symbols.getFunction(id)) =>
        val tfd = symbols.getFunction(id, tps)
        transform(s.exprOps.freshenLocals(
          s.exprOps.replaceFromSymbols((tfd.params zip args).toMap, tfd.fullBody))).setPos(e)
      case other => super.transform(other)
    }

    override def transform(fd: s.FunDef): t.FunDef = {
      super.transform(fd.copy(flags = fd.flags.flatMap {
        case IsAccessor(_) => Some(Annotation("accessor", Seq.empty))
        case IsAbstract => None
        case other => Some(other)
      }))
    }
  }

  override protected type FunctionResult = Option[t.FunDef]

  // The field types depend on the accessors and dispatchers that are inlined in them
  override protected final val classCache = new ExtractionCache[s.ClassDef, (ClassResult, ClassSummary)]({
    (cd, ctx) => ClassKey(cd) + SetKey(ctx.fieldTypeInlinings(cd).map(id => FunctionKey(ctx.symbols.getFunction(id)): CacheKey))
  })

  // The transformation depends on all (transitive) accessors that will be inlined
  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]({
    (fd, ctx) => FunctionKey(fd) + SetKey(ctx.symbols.dependencies(fd.id)
      .flatMap(id => ctx.symbols.lookupFunction(id))
      .filter(fd => ctx.isConcreteAccessor(fd) || ctx.isAccessorDispatcher(fd))
      .map(_.id)
    )(using ctx.symbols)
  })

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (Option[t.FunDef], Unit) =
    (if (context.isConcreteAccessor(fd)) None else Some(context.transform(fd)), ())

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort) = (context.transform(sort), ())
  override protected def extractClass(context: TransformerContext, cd: s.ClassDef) = (context.inFieldTypesContext.transform(cd), ())
}

object FieldAccessors {
  def apply(tr: Trees)(using inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = {
    class Impl(override val s: tr.type, override val t: tr.type) extends FieldAccessors(s, t)
    new Impl(tr, tr)
  }
}
