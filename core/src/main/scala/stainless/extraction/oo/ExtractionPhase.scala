/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

trait CachingPhase extends extraction.CachingPhase { self =>
  protected val s: Trees
  protected val t: Trees

  protected type ClassResult
  private lazy val classCache = new ExtractionCache[s.ClassDef, ClassResult]

  protected def transformClass(context: TransformerContext, cd: s.ClassDef): ClassResult
  protected def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols

  override protected def transformSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    registerClasses(
      super.transformSymbols(context, symbols),
      symbols.classes.values.map { cd =>
        classCache.cached(cd, symbols)(transformClass(context, cd))
      }.toSeq
    )
  }
}

trait SimpleClasses extends CachingPhase {
  override protected type ClassResult = t.ClassDef
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[t.ClassDef]): t.Symbols = symbols.withClasses(classes)
}

trait IdentityClasses extends SimpleClasses { self =>
  private[this] final object identity extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def transformFunction(context: TransformerContext, cd: s.ClassDef): t.ClassDef = identity.transform(cd)
}

trait SimplePhase extends CachingPhase with extraction.SimplePhase with SimpleClasses { self =>
  override protected type TransformerContext = oo.TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def transformClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = context.transform(cd)
}
