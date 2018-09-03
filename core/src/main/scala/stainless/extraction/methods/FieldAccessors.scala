/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import scala.language.existentials

trait FieldAccessors extends oo.CachingPhase
  with SimplyCachedFunctions
  with IdentitySorts
  with oo.IdentityClasses { self =>

  val s: Trees
  val t: Trees
  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(symbols: s.Symbols) extends ast.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    import symbols.simplifyExpr

    def isConcreteAccessor(id: Identifier): Boolean = {
      isConcreteAccessor(symbols.functions(id))
    }

    def isConcreteAccessor(fd: s.FunDef): Boolean = {
      val isAccessor = fd.flags exists { case s.IsAccessor(_) => true case _ => false }
      val isAbstract = fd.flags contains s.IsAbstract

      isAccessor && !isAbstract
    }

    private[this] implicit val popts = inox.solvers.PurityOptions(context)

    override def transform(e: s.Expr): t.Expr = e match {
      case mi: MethodInvocation if isConcreteAccessor(mi.id) =>
        transform(simplifyExpr(mi.inlined(symbols)))
      case fi: FunctionInvocation if isConcreteAccessor(fi.id) =>
        transform(simplifyExpr(fi.inlined(symbols)))
      case other => super.transform(other)
    }
  }

  override protected type FunctionResult = Option[t.FunDef]

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): Option[t.FunDef] =
    if (context.isConcreteAccessor(fd)) None else Some(context.transform(fd))

}

object FieldAccessors {
  def apply(ts: Trees, tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new FieldAccessors {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
