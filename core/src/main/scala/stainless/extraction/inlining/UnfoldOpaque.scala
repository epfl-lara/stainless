/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package inlining

class UnfoldOpaque(override val s: Trees, override val t: Trees)
                  (using override val context: inox.Context) extends CachingPhase with NoSummaryPhase with SimpleFunctions with IdentitySorts { self =>

  override protected final val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  protected class TransformerContext(override val s: self.s.type,
                                     override val t: self.t.type,
                                     val symbols: self.s.Symbols) extends inox.transformers.Transformer with inox.transformers.DefinitionTransformer {
    def this(symbols: self.s.Symbols) = this(self.s, self.t, symbols)
    override type Env = Map[s.Variable, s.Expr]

    import s._
    import symbols.{given, _}

    override def initEnv: Env = Map.empty

    override def transform(e: Expr, env: Env): t.Expr = {
      e match {
        case s.FunctionInvocation(ast.SymbolIdentifier("stainless.lang.unfolding"), Seq(_), Seq(maybeFi)) =>
          // Lookup the bindings recursively to unveil a call to a function which we would need to unfold
          val r = dealiasedAndStripped(maybeFi, env)
          r match {
            case fi: FunctionInvocation =>
              val newFi = transform(fi, env)
              val inlined = transform(fi.inlined, env)
              val specced = t.exprOps.BodyWithSpecs(inlined)
              t.Assume(t.Equals(newFi, t.annotated(specced.letsAndBody, t.DropVCs)).setPos(e), t.UnitLiteral().setPos(e)).setPos(e)
            case _ => super.transform(e, env)
          }
        case Let(v, e2, body) =>
          val vRec = transform(v, env)
          val eRec = transform(e2, env)
          val eBody = transform(body, env + (v.toVariable -> e2))
          t.Let(vRec, eRec, eBody).setPos(e)
        case _ => super.transform(e, env)
      }
    }

    def dealiasedAndStripped(e: Expr, env: Env): Expr = {
      e match {
        case v: Variable => env.get(v).map(dealiasedAndStripped(_, env)).getOrElse(v)
        case TupleSelect(tuple, index) =>
          dealiasedAndStripped(tuple, env) match {
            case Tuple(es) => dealiasedAndStripped(es(index - 1), env)
            case _ => e
          }
        case Annotated(body, _) => dealiasedAndStripped(body, env)
        case _ => e
      }
    }
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) = {
    (context.transform(fd), ())
  }

}

object UnfoldOpaque {
  def apply(it: inlining.Trees)(using inox.Context): ExtractionPipeline {
    val s: it.type
    val t: it.type
  } = {
    class Impl(override val s: it.type, override val t: it.type) extends UnfoldOpaque(s, t)
    new Impl(it, it)
  }
}
