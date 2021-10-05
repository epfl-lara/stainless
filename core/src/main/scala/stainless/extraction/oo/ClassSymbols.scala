/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait ClassSymbols { self1: Trees =>

  val Symbols: (
    Map[Identifier, FunDef],
    Map[Identifier, ADTSort],
    Map[Identifier, ClassDef],
    Map[Identifier, TypeDef],
  ) => Symbols

  val NoSymbols = Symbols(Map.empty, Map.empty, Map.empty, Map.empty)

  abstract class ClassSymbols extends AbstractSymbols { self2: Symbols =>

    def withFunctions(functions: Seq[FunDef]): Symbols = Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.sorts,
      this.classes,
      this.typeDefs,
    )

    def withSorts(sorts: Seq[ADTSort]): Symbols = Symbols(
      this.functions,
      this.sorts ++ sorts.map(sort => sort.id -> sort),
      this.classes,
      this.typeDefs,
    )

    def withClasses(classes: Seq[ClassDef]): Symbols = Symbols(
      this.functions,
      this.sorts,
      this.classes ++ classes.map(cd => cd.id -> cd),
      this.typeDefs,
    )

    def withTypeDefs(typeDefs: Seq[TypeDef]): Symbols = Symbols(
      this.functions,
      this.sorts,
      this.classes,
      this.typeDefs ++ typeDefs.map(td => td.id -> td),
    )

    def ++(other: ClassSymbols) = Symbols(
      this.functions ++ other.functions,
      this.sorts ++ other.sorts,
      this.classes ++ other.classes,
      this.typeDefs ++ other.typeDefs,
    )

    override def astSize: Int = {
      var result = 0
      val counter = new oo.TreeTraverser {
        val trees: self1.type = self1

        override def traverse(fd: FunDef) = { result += 1; super.traverse(fd) }
        override def traverse(cd: ClassDef) = { result += 1; super.traverse(cd) }
        override def traverse(sort: ADTSort) = { result += 1; super.traverse(sort) }
        override def traverse(e: Expr) = { result += 1; super.traverse(e) }
        override def traverse(tpe: Type) = { result += 1; super.traverse(tpe) }
        override def traverse(pattern: Pattern) = { result += 1; super.traverse(pattern) }
        override def traverse(vd: ValDef) = { result += 1; super.traverse(vd) }
        override def traverse(id: Identifier): Unit = { result += 1; super.traverse(id) }
        override def traverse(tpd: TypeParameterDef): Unit = { result += 1; super.traverse(tpd) }
        override def traverse(flag: Flag): Unit = { result += 1; super.traverse(flag) }
      }

      symbols.functions.values.foreach(counter.traverse)
      symbols.classes.values.foreach(counter.traverse)
      symbols.sorts.values.foreach(counter.traverse)
      symbols.typeDefs.values.foreach(counter.traverse)

      result
    }
  }
}
