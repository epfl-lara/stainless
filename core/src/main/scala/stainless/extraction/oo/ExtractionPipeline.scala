/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

trait ExtractionPipeline extends extraction.ExtractionPipeline {
  val s: Trees
}

trait CachingPhase extends ExtractionPipeline with extraction.CachingPhase with ExtractionCaches { self =>
  protected type ClassResult
  protected val classCache: ExtractionCache[s.ClassDef, ClassResult]

  protected def extractClass(context: TransformerContext, cd: s.ClassDef): ClassResult
  protected def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    registerClasses(
      super.extractSymbols(context, symbols),
      symbols.classes.values.map { cd =>
        classCache.cached(cd, symbols)(extractClass(context, cd))
      }.toSeq
    )
  }
}

trait SimpleClasses extends CachingPhase {
  val t: Trees

  override protected type ClassResult = t.ClassDef
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[t.ClassDef]): t.Symbols = symbols.withClasses(classes)
}

trait SimplyCachedClasses extends CachingPhase {
  override protected final val classCache: ExtractionCache[s.ClassDef, ClassResult] = new SimpleCache[s.ClassDef, ClassResult]
}

trait DependentlyCachedClasses extends CachingPhase {
  override protected final val classCache: ExtractionCache[s.ClassDef, ClassResult] = new DependencyCache[s.ClassDef, ClassResult]
}

trait IdentityClasses extends SimpleClasses with SimplyCachedClasses { self =>
  private[this] final object identity extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = identity.transform(cd)
}

trait SimplePhase extends CachingPhase with extraction.SimplePhase with SimpleClasses { self =>
  protected type TransformerContext <: oo.TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = context.transform(cd)
}
