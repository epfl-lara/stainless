/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

trait ClassSymbols { self: Trees =>

  val Symbols: (
    Map[Identifier, FunDef],
    Map[Identifier, ADTSort],
    Map[Identifier, ClassDef],
    Map[Identifier, TypeDef],
  ) => Symbols

  val NoSymbols = Symbols(Map.empty, Map.empty, Map.empty, Map.empty)

  abstract class ClassSymbols extends AbstractSymbols { self: Symbols =>

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
  }
}
