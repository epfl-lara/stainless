/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

trait ClassSymbols { self: Trees =>

  val Symbols: (Map[Identifier, FunDef], Map[Identifier, ADTSort], Map[Identifier, ClassDef]) => Symbols

  val NoSymbols = Symbols(Map.empty, Map.empty, Map.empty)

  abstract class ClassSymbols extends AbstractSymbols { self: Symbols =>

    def withFunctions(functions: Seq[FunDef]): Symbols = Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.sorts,
      this.classes
    )

    def withSorts(sorts: Seq[ADTSort]): Symbols = Symbols(
      this.functions,
      this.sorts ++ sorts.map(sort => sort.id -> sort),
      this.classes
    )

    def withClasses(classes: Seq[ClassDef]): Symbols = Symbols(
      this.functions,
      this.sorts,
      this.classes ++ classes.map(cd => cd.id -> cd)
    )

    override def filterObjects(objs: Set[String]) = {
      NoSymbols.
        withFunctions(this.functions.values.toSeq.filter { fd => objs.contains(fd.id.name) }).
        withSorts(this.sorts.values.toSeq.filter { s => objs.contains(s.id.name) }).
        withClasses(this.classes.values.toSeq.filter { cd => objs.contains(cd.id.name) })
    }
  }
}
