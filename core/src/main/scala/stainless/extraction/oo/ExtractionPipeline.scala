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
  protected type ClassSummary
  protected val classCache: ExtractionCache[s.ClassDef, (ClassResult, ClassSummary)]

  protected type TypeDefResult
  protected type TypeDefSummary
  protected val typeDefCache: ExtractionCache[s.TypeDef, (TypeDefResult, TypeDefSummary)]

  protected def extractClass(context: TransformerContext, cd: s.ClassDef): (ClassResult, ClassSummary)
  protected def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols

  protected def extractTypeDef(context: TransformerContext, cd: s.TypeDef): (TypeDefResult, TypeDefSummary)
  protected def registerTypeDefs(symbols: t.Symbols, typeDefs: Seq[TypeDefResult]): t.Symbols

  class OOAllSummaries(
    fnsSummary: Seq[FunctionSummary] = Seq.empty,
    sortsSummary: Seq[SortSummary] = Seq.empty,
    val classesSummaries: Seq[ClassSummary] = Seq.empty,
    val typeDefsSummaries: Seq[TypeDefSummary] = Seq.empty,
  ) extends AllSummaries(fnsSummary, sortsSummary)

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): (t.Symbols, OOAllSummaries) = {
    val (superSyms, superSummaries) = super.extractSymbols(context, symbols)

    val (classes, classesSummaries) = symbols.classes.values.map { cd =>
      classCache.cached(cd, context)(extractClass(context, cd))
    }.toSeq.unzip
    val withClasses = registerClasses(superSyms, classes)
    val (typeDefs, typeDefsSummaries) = symbols.typeDefs.values.map { td =>
      typeDefCache.cached(td, context)(extractTypeDef(context, td))
    }.toSeq.unzip
    val withTypeDefs = registerTypeDefs(withClasses, typeDefs)
    (withTypeDefs, OOAllSummaries(superSummaries.fnsSummary, superSummaries.sortsSummary, classesSummaries, typeDefsSummaries))
  }
}

trait SimpleClasses extends CachingPhase {
  val t: Trees

  override protected type ClassResult = t.ClassDef
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[t.ClassDef]): t.Symbols = symbols.withClasses(classes)
}

trait SimplyCachedClasses extends CachingPhase {
  override protected final val classCache: ExtractionCache[s.ClassDef, (ClassResult, ClassSummary)] = new SimpleCache
}

trait IdentityClasses extends SimpleClasses with SimplyCachedClasses { self =>
  override protected type ClassSummary = Unit

  private[this] class IdentityImpl(override val s: self.s.type, override val t: self.t.type) extends oo.ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentityImpl(s, t)

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): (t.ClassDef, Unit) = (identity.transform(cd), ())
}

trait SimpleTypeDefs extends CachingPhase {
  val t: Trees

  override protected type TypeDefResult = t.TypeDef
  override protected def registerTypeDefs(symbols: t.Symbols, classes: Seq[t.TypeDef]): t.Symbols = symbols.withTypeDefs(classes)
}

trait SimplyCachedTypeDefs extends CachingPhase {
  override protected final val typeDefCache: ExtractionCache[s.TypeDef, (TypeDefResult, TypeDefSummary)] = new SimpleCache
}

trait IdentityTypeDefs extends SimpleTypeDefs with SimplyCachedTypeDefs { self =>
  override protected type TypeDefSummary = Unit

  private[this] class IdentityTypeDefsImpl(override val s: self.s.type, override val t: self.t.type) extends oo.ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentityTypeDefsImpl(s, t)

  override protected def extractTypeDef(context: TransformerContext, td: s.TypeDef): (t.TypeDef, Unit) = (identity.transform(td), ())
}

trait NoSummaryPhase extends CachingPhase with extraction.NoSummaryPhase {
  override protected type ClassSummary = Unit
  override protected type TypeDefSummary = Unit
}

trait SimplePhase extends CachingPhase with extraction.SimplePhase with SimpleClasses with SimpleTypeDefs with NoSummaryPhase { self =>
  protected type TransformerContext <: oo.TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): (t.ClassDef, Unit) = (context.transform(cd), ())
  override protected def extractTypeDef(context: TransformerContext, td: s.TypeDef): (t.TypeDef, Unit) = (context.transform(td), ())
}
