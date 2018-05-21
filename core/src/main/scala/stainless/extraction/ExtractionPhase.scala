/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.collection.mutable.{Map => MutableMap}

trait ExtractionPhase { self =>
  protected val s: ast.Trees
  protected val t: ast.Trees

  protected def lastSymbols(id: Identifier): s.Symbols

  def nextSymbols(id: Identifier): t.Symbols
}

trait PipelinePhase extends ExtractionPhase { self =>
  protected val previous: ExtractionPhase { val t: self.s.type }

  override protected final def lastSymbols(id: Identifier): s.Symbols = previous.nextSymbols(id)
}

trait SimplePhase extends ExtractionPhase { self =>
  private[this] val functionCache: MutableMap[Identifier, t.FunDef] = MutableMap.empty
  private[this] val sortCache: MutableMap[Identifier, t.ADTSort] = MutableMap.empty

  protected def transformSymbols(symbols: s.Symbols): t.Symbols = t.NoSymbols
    .withFunctions(symbols.functions.values.toSeq.map { fd =>
      functionCache.getOrElseUpdate(fd.id, transformFunction(symbols, fd))
    })
    .withSorts(symbols.sorts.values.toSeq.map { sort =>
      sortCache.getOrElseUpdate(sort.id, transformSort(symbols, sort))
    })

  private[this] class DefaultTransformer extends ast.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t
  }

  protected def transformFunction(symbols: s.Symbols, fd: s.FunDef): t.FunDef =
    new DefaultTransformer().transform(fd)

  protected def transformSort(symbols: s.Symbols, sort: s.ADTSort): t.ADTSort =
    new DefaultTransformer().transform(sort)

  override final def nextSymbols(id: Identifier): t.Symbols = transformSymbols(lastSymbols(id))
}

trait SimpleOOPhase extends SimplePhase { self =>
  protected val s: oo.Trees
  protected val t: oo.Trees

  private[this] class DefaultTransformer extends oo.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t
  }

  private[this] val classCache: MutableMap[Identifier, t.ClassDef] = MutableMap.empty
  override protected def transformSymbols(symbols: s.Symbols): t.Symbols =
    super.transformSymbols(symbols)
      .withClasses(symbols.classes.values.toSeq.map { cd =>
        classCache.getOrElseUpdate(cd.id, transformClass(symbols, cd))
      })

  protected def transformClass(symbols: s.Symbols, cd: s.ClassDef): t.ClassDef =
    new DefaultTransformer().transform(cd)
}
