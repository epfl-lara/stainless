/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package termination

trait SizedADTExtraction extends SimplePhase
  with SimplyCachedFunctions
  with IdentitySorts
  { self =>
  val s: Trees
  val t: s.type

  import s._
  import s.exprOps._

  protected class TransformerContext(implicit symbols: Symbols) extends transformers.TreeTransformer {
    val s: self.s.type = self.s
    val t: s.type = s

    override def transform(e: Expr) = e match {
      case FunctionInvocation(
        ast.SymbolIdentifier("stainless.lang.indexedAt"),
        Seq(_),
        Seq(n, ADT(id, tps, args))
      ) => SizedADT(transform(id), tps.map(transform), args.map(transform), transform(n))

      case _ => super.transform(e)
    }

    override def transform(tpe: Type) = tpe match {
      case AnnotatedType(adt@ADTType(id, tps), flags) =>
        flags.collectFirst {
          case IndexedAt(n) =>
            AnnotatedType(
              RecursiveType(transform(id), tps.map(transform), transform(n)),
              flags.filter { case IndexedAt(_) => false case _ => true }
            )
        }.getOrElse(super.transform(tpe))
      case _ => super.transform(tpe)
    }
  }

  override protected def getContext(syms: Symbols) = new TransformerContext()(syms)
}

object SizedADTExtraction {
  def apply(tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = new SizedADTExtraction {
    override val s: tt.type = tt
    override val t: tt.type = tt
    override val context = ctx
  }
}
