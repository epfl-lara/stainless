/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package methods

import scala.language.existentials

trait FieldAccessors extends oo.CachingPhase
  with SimpleSorts
  with oo.SimpleClasses
  with SimplyCachedSorts
  with oo.IdentityTypeDefs
  with oo.SimplyCachedClasses { self =>

  val s: Trees
  val t: oo.Trees
  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) extends oo.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    implicit private val syms = symbols

    def dropAccessor(fd: FunDef): Boolean = isConcreteAccessor(fd) || isExternAccessor(fd)
    def isConcreteAccessor(fd: FunDef): Boolean = fd.isAccessor && !fd.isAbstract
    def isExternAccessor(fd: FunDef): Boolean = fd.isAccessor && fd.isExtern

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
      .filter(ctx.dropAccessor)
      .map(_.id)
    )(ctx.symbols)
  })

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): Option[t.FunDef] =
    if (context.dropAccessor(fd)) None else Some(context.transform(fd))

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort) = context.transform(sort)
  override protected def extractClass(context: TransformerContext, cd: s.ClassDef) = context.transform(cd)
}

object FieldAccessors {
  def apply(tr: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new FieldAccessors {
    override val s: tr.type = tr
    override val t: tr.type = tr
    override val context = ctx
  }
}
