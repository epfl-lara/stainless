/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package xlang

trait XlangNormalizer extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: oo.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    object transformer extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    }

    t.NoSymbols
      .withFunctions(symbols.functions.values.toSeq.map(fd => transformer.transform(fd.copy(
        flags = fd.flags.filter {
          case s.IsField(_) | s.Ignore | s.Inline => false
          case _ => true
        }
      ))))
      .withADTs(symbols.adts.values.toSeq.map(adt => transformer.transform(adt match {
        case sort: s.ADTSort => sort.copy(flags = adt.flags - s.Ignore)
        case cons: s.ADTConstructor => cons.copy(flags = adt.flags - s.Ignore)
      })))
      .withClasses(symbols.classes.values.toSeq.map(cd => new t.ClassDef(
        cd.id,
        transformer.transformTypeParams(cd.tparams),
        cd.parent,
        cd.fields.map(transformer.transform),
        cd.methods,
        (cd.flags - s.Ignore).map(transformer.transform)
      )))
  }
}
