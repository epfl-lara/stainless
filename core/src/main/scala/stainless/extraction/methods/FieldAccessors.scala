/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

class FieldAccessors(override val s: Trees, override val t: oo.Trees)
                    (using override val context: inox.Context)
  extends oo.CachingPhase
     with SimpleSorts
     with oo.SimpleClasses
     with SimplyCachedSorts
     with oo.IdentityTypeDefs
     with oo.SimplyCachedClasses { self =>

  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(self.s, self.t, symbols)

  protected class TransformerContext(override val s: self.s.type,
                                     override val t: self.t.type,
                                     val symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) {
    import symbols.{given, _}

    def isConcreteAccessor(fd: FunDef): Boolean = fd.isAccessor && !fd.isAbstract && !fd.body.isEmpty

    override def transform(e: s.Expr): t.Expr = e match {
      case FunctionInvocation(id, tps, args) if isConcreteAccessor(symbols.getFunction(id)) =>
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

  // The transformation depends on all (transitive) accessors that will be inlined
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({
    (fd, ctx) => FunctionKey(fd) + SetKey(ctx.symbols.dependencies(fd.id)
      .flatMap(id => ctx.symbols.lookupFunction(id))
      .filter(ctx.isConcreteAccessor)
      .map(_.id)
    )(using ctx.symbols)
  })

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): Option[t.FunDef] =
    if (context.isConcreteAccessor(fd)) None else Some(context.transform(fd))

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort) = context.transform(sort)
  override protected def extractClass(context: TransformerContext, cd: s.ClassDef) = context.transform(cd)
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
