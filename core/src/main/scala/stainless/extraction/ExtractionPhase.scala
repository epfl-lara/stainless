/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.collection.mutable.{Map => MutableMap}

trait ExtractionPhase { self =>
  val s: ast.Trees
  val t: ast.Trees

  implicit val context: inox.Context
  protected implicit def printerOpts: s.PrinterOptions = s.PrinterOptions.fromContext(context)

  protected def lastSymbols(id: Identifier): s.Symbols

  def nextSymbols(id: Identifier): t.Symbols
}

trait PipelinePhase extends ExtractionPhase { self =>
  protected val previous: ExtractionPhase { val t: self.s.type }

  override protected final def lastSymbols(id: Identifier): s.Symbols = previous.nextSymbols(id)
}

trait PipelineBuilder { self =>
  val s: ast.Trees
  val t: ast.Trees

  def build(previous: ExtractionPhase { val t: self.s.type }): ExtractionPhase {
    val s: previous.s.type
    val t: self.t.type
  }

  def andThen(that: PipelineBuilder { val s: self.t.type }): PipelineBuilder {
    val s: self.s.type
    val t: that.t.type
  } = new PipelineBuilder {
    override val s: self.s.type = self.s
    override val t: that.t.type = that.t

    override def build(previous: ExtractionPhase { val t: self.s.type }): ExtractionPhase {
      val s: previous.s.type
      val t: that.t.type
    } = that.build(self.build(previous))
  }
}

object PipelineBuilder {
  def apply(ts: ast.Trees, tt: ast.Trees)(
    // @nv: We actually need a dependent function type here but these are not easily expressible
    //      in scala, so we use this weaker API with an asInstanceOf cast.
    // Actual expected parameter type:
    //   (prev: ExtractionPhase { val t: ts.type }) => ExtractionPhase { val s: prev.s.type; val t: tt.type }
    builder: (ExtractionPhase { val t: ts.type }) => ExtractionPhase { val t: tt.type }
  ): PipelineBuilder { val s: ts.type; val t: tt.type } = new PipelineBuilder {
    val s: ts.type = ts
    val t: tt.type = tt

    override def build(previous: ExtractionPhase { val t: ts.type }): ExtractionPhase {
      val s: previous.s.type
      val t: tt.type
    } = builder(previous).asInstanceOf[ExtractionPhase {
      val s: previous.s.type
      val t: tt.type
    }]
  }
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

  protected def transformer: ast.TreeTransformer { val s: self.s.type; val t: self.t.type } =
    new ast.TreeTransformer {
      override final val s: self.s.type = self.s
      override final val t: self.t.type = self.t
    }

  protected def transformFunction(symbols: s.Symbols, fd: s.FunDef): t.FunDef = transformer.transform(fd)
  protected def transformSort(symbols: s.Symbols, sort: s.ADTSort): t.ADTSort = transformer.transform(sort)

  override final def nextSymbols(id: Identifier): t.Symbols = transformSymbols(lastSymbols(id))
}

trait SimpleOOPhase extends SimplePhase { self =>
  val s: oo.Trees
  val t: oo.Trees

  protected def transformer: oo.TreeTransformer { val s: self.s.type; val t: self.t.type } =
    new oo.TreeTransformer {
      override final val s: self.s.type = self.s
      override final val t: self.t.type = self.t
    }

  private[this] val classCache: MutableMap[Identifier, t.ClassDef] = MutableMap.empty
  override protected def transformSymbols(symbols: s.Symbols): t.Symbols =
    super.transformSymbols(symbols)
      .withClasses(symbols.classes.values.toSeq.map { cd =>
        classCache.getOrElseUpdate(cd.id, transformClass(symbols, cd))
      })

  protected def transformClass(symbols: s.Symbols, cd: s.ClassDef): t.ClassDef = transformer.transform(cd)
}
