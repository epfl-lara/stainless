/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait InvariantInitialization
  extends CachingPhase
     with IdentityFunctions
     with IdentityClasses
     with IdentityTypeDefs { self =>

  val s: Trees
  val t: Trees

  override protected final def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)
  protected final class TransformerContext(implicit val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    val paramInitsMap: Map[s.ADTConstructor, Seq[s.FunDef]] = {
      symbols.sorts.values.flatMap { sort =>
        sort.constructors.map { constructor =>
          constructor -> symbols.paramInits(constructor.id)
        }
      }.toMap
    }
  }

  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult]({
    (sort, context) => SortKey(sort) + SetKey(sort.constructors.flatMap { constructor =>
      context.paramInitsMap(constructor).toSet
    }.toSet)
  })

  override protected final type SortResult = (t.ADTSort, Seq[t.FunDef])
  override protected final def registerSorts(symbols: t.Symbols, sortResults: Seq[SortResult]): t.Symbols = {
    sortResults.foldLeft(symbols) {
      case (symbols, (sort, fds)) => symbols.withSorts(Seq(sort)).withFunctions(fds)
    }
  }

  override protected final def extractSort(context: TransformerContext, sort: s.ADTSort): SortResult = {
    val sort2 = context.transform(sort)
    val initializationChecks =
      for (
        constructor <- sort.constructors
        if sort.tparams.isEmpty
        if constructor.fields.length == context.paramInitsMap(constructor).length
      ) yield {
        val adtType = t.ADTType(sort2.id, Seq())
        new t.FunDef(
          FreshIdentifier(constructor.id + "RequireForDefault"),
          Seq(),
          Seq(),
          t.UnitType().setPos(constructor),
          t.Let(t.ValDef.fresh("unused", adtType).setPos(constructor),
            t.ADT(constructor.id,
              Seq(),
              context.paramInitsMap(constructor).map(fd => t.FunctionInvocation(fd.id, Seq(), Seq()).setPos(constructor))
            ).setPos(constructor),
            t.UnitLiteral().setPos(constructor)
          ).setPos(constructor),
          Seq(t.Derived(None)),
        ).setPos(constructor)
      }
    (sort2, initializationChecks)
  }
}

object InvariantInitialization {
  def apply(ts: Trees, tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new {
    override val s: ts.type = ts
    override val t: tt.type = tt
  } with InvariantInitialization {
    override val context = ctx
  }
}
