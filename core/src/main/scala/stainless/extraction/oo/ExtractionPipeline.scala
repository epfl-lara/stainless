/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait ExtractionPipeline extends extraction.ExtractionPipeline {
  val s: Trees
}

trait ExtractionContext extends ExtractionPipeline with extraction.ExtractionContext

trait CachingPhase extends ExtractionContext with extraction.CachingPhase with ExtractionCaches { self =>
  protected type ClassResult
  protected val classCache: ExtractionCache[s.ClassDef, ClassResult]

  protected type TypeDefResult
  protected val typeDefCache: ExtractionCache[s.TypeDef, TypeDefResult]

  protected def extractClass(context: TransformerContext, cd: s.ClassDef): ClassResult
  protected def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols

  protected def extractTypeDef(context: TransformerContext, cd: s.TypeDef): TypeDefResult
  protected def registerTypeDefs(symbols: t.Symbols, typeDefs: Seq[TypeDefResult]): t.Symbols

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val withClasses = registerClasses(
      super.extractSymbols(context, symbols),
      symbols.classes.values.map { cd =>
        classCache.cached(cd, context)(extractClass(context, cd))
      }.toSeq
    )

    registerTypeDefs(
      withClasses,
      symbols.typeDefs.values.map { td =>
        typeDefCache.cached(td, context)(extractTypeDef(context, td))
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

trait IdentityClasses extends SimpleClasses with SimplyCachedClasses { self =>
  private[this] class IdentityImpl(override val s: self.s.type, override val t: self.t.type) extends oo.ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentityImpl(s, t)

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = identity.transform(cd)
}

trait SimpleTypeDefs extends CachingPhase {
  val t: Trees

  override protected type TypeDefResult = t.TypeDef
  override protected def registerTypeDefs(symbols: t.Symbols, classes: Seq[t.TypeDef]): t.Symbols = symbols.withTypeDefs(classes)
}

trait SimplyCachedTypeDefs extends CachingPhase {
  override protected final val typeDefCache: ExtractionCache[s.TypeDef, TypeDefResult] = new SimpleCache[s.TypeDef, TypeDefResult]
}

trait IdentityTypeDefs extends SimpleTypeDefs with SimplyCachedTypeDefs { self =>
  private[this] class IdentityTypeDefsImpl(override val s: self.s.type, override val t: self.t.type) extends oo.ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentityTypeDefsImpl(s, t)

  override protected def extractTypeDef(context: TransformerContext, td: s.TypeDef): t.TypeDef = identity.transform(td)
}

trait SimplePhase extends CachingPhase with extraction.SimplePhase with SimpleClasses with SimpleTypeDefs { self =>
  protected type TransformerContext <: oo.TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = context.transform(cd)
  override protected def extractTypeDef(context: TransformerContext, td: s.TypeDef): t.TypeDef = context.transform(td)
}
