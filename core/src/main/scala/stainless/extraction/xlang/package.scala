/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

package object xlang {

  object trees extends xlang.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: xlang.trees.type = xlang.trees }
  }

  /** As `xlang.Trees` don't extend the supported ASTs, the transformation from
    * these trees to `oo.Trees` simply consists in an identity mapping. */
  object extractor extends oo.SimpleSymbolTransformer {
    val s: trees.type = trees
    val t: anon.trees.type = anon.trees

    object transformer extends ast.TreeTransformer {
      val s: trees.type = trees
      val t: anon.trees.type = anon.trees
    }

    def transformFunction(fd: s.FunDef): t.FunDef = transformer.transform(fd.copy(
      flags = fd.flags.filter {
        case s.Ignore => false
        case _ => true
      }))

    def transformSort(sort: s.ADTSort): t.ADTSort = transformer.transform(sort.copy(
      flags = sort.flags filterNot (_ == s.Ignore)
    ))

    def transformClass(cd: s.ClassDef): t.ClassDef = new t.ClassDef(
      cd.id,
      cd.tparams.map(tdef => transformer.transform(tdef)),
      cd.parents.map(ct => transformer.transform(ct).asInstanceOf[t.ClassType]),
      cd.fields.map(vd => transformer.transform(vd)),
      cd.flags filterNot (_ == s.Ignore) map transformer.transform
    ).copiedFrom(cd)
  }
}
