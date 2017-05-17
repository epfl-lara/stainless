/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

package object xlang {

  object trees extends xlang.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: xlang.trees.type = xlang.trees }
  }

  /** As `xlang.Trees` don't extend the supported ASTs, the transformation from
    * these trees to `oo.Trees` simply consists in an identity mapping. */
  object extractor extends oo.SimpleSymbolTransformer {
    val s: trees.type = trees
    val t: oo.trees.type = oo.trees

    object transformer extends ast.TreeTransformer {
      val s: trees.type = trees
      val t: oo.trees.type = oo.trees
    }

    def transformFunction(fd: s.FunDef): t.FunDef = transformer.transform(fd.copy(
      flags = fd.flags.filter {
        case s.IsField(_) | s.Ignore => false
        case _ => true
      }))

    def transformADT(adt: s.ADTDefinition): t.ADTDefinition = transformer.transform(adt match {
      case sort: s.ADTSort => sort.copy(flags = adt.flags - s.Ignore)
      case cons: s.ADTConstructor => cons.copy(flags = adt.flags - s.Ignore)
    })

    def transformClass(cd: s.ClassDef): t.ClassDef = new t.ClassDef(
      cd.id,
      cd.tparams.map(tdef => transformer.transform(tdef)),
      cd.parents.map(ct => transformer.transform(ct).asInstanceOf[t.ClassType]),
      cd.fields.map(vd => transformer.transform(vd)),
      (cd.flags - s.Ignore).map(f => transformer.transform(f))
    ).copiedFrom(cd)
  }
}
