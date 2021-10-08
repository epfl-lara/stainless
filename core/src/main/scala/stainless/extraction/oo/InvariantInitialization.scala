/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

class InvariantInitialization(override val s: Trees, override val t: Trees)
                             (using override val context: inox.Context)
  extends CachingPhase
     with IdentityFunctions
     with IdentityClasses
     with IdentityTypeDefs { self =>

  override protected final def getContext(symbols: s.Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  protected final class TransformerContext(override val s: self.s.type, override val t: self.t.type)
                                          (using val symbols: s.Symbols) extends oo.ConcreteTreeTransformer(s, t) {
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
          FreshIdentifier(s"${constructor.id}RequireForDefault"),
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
  def apply(ts: Trees, tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends InvariantInitialization(s, t)
    new Impl(ts, tt)
  }
}
