/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package termination

class SizedADTExtraction(override val s: Trees)(override val t: s.type)
                        (using override val context: inox.Context)
  extends SimplePhase
     with SimplyCachedFunctions
     with IdentitySorts { self =>

  import s._
  import s.exprOps._

  protected class TransformerContext(override val s: self.s.type, override val t: s.type)
                                    (using symbols: Symbols) extends transformers.ConcreteTreeTransformer(s, t) {
    override def transform(e: Expr) = e match {
      case FunctionInvocation(
          ast.SymbolIdentifier("stainless.lang.indexedAt"),
          Seq(_),
          Seq(n, ADT(id, tps, args))
          ) =>
        SizedADT(transform(id), tps.map(transform), args.map(transform), transform(n))

      case FunctionInvocation(ast.SymbolIdentifier("stainless.lang.indexedAt"), _, _) =>
        context.reporter.fatalError(e.getPos,
          "The `indexedAt` construct should be used as follows: `indexedAt(n, C(...))` " +
          "where `n` is a non-negative BigInt, and `C` is an ADT constructor")

      case _ => super.transform(e)
    }

    override def transform(tpe: Type) = tpe match {
      case AnnotatedType(adt @ ADTType(id, tps), flags) =>
        flags
          .collectFirst {
            case IndexedAt(n) =>
              AnnotatedType(
                RecursiveType(transform(id), tps.map(transform), transform(n)),
                flags.filter {
                  case IndexedAt(_) => false
                  case _            => true
                }
              )
          }
          .getOrElse(super.transform(tpe))
      case _ => super.transform(tpe)
    }
  }

  override protected def getContext(syms: Symbols) = new TransformerContext(self.s, self.t)(using syms)
}

object SizedADTExtraction {
  def apply(tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = {
    class Impl(override val s: tt.type, override val t: tt.type) extends SizedADTExtraction(s)(t)
    new Impl(tt, tt)
  }
}
