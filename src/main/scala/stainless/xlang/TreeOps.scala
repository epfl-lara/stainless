/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

trait SymbolTransformer extends inox.ast.SymbolTransformer {
  val transformer: inox.ast.TreeTransformer { val s: Trees; val t: Trees }

  override def transform(syms: s.Symbols): t.Symbols =
    super.transform(syms).withClasses(syms.classes.values.toSeq.map(cd => new t.ClassDef(
      cd.id,
      transformTypeParams(cd.tparams),
      cd.parent,
      cd.fields.map(vd => transformer.transform(vd)),
      cd.methods,
      cd.flags.map(f => transformer.transform(f))
    )))
}
