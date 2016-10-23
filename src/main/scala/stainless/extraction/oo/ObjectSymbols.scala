/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

trait ObjectSymbols { self: Trees =>

  val Symbols: (Map[Identifier, FunDef], Map[Identifier, ADTDefinition], Map[Identifier, ClassDef]) => Symbols

  val NoSymbols = Symbols(Map.empty, Map.empty, Map.empty)

  abstract class ObjectSymbols extends AbstractSymbols { self: Symbols =>

    def withFunctions(functions: Seq[FunDef]): Symbols = Symbols(
      this.functions ++ functions.map(fd => fd.id -> fd),
      this.adts,
      this.classes
    )

    def withADTs(adts: Seq[ADTDefinition]): Symbols = Symbols(
      this.functions,
      this.adts ++ adts.map(adt => adt.id -> adt),
      this.classes
    )

    def withClasses(classes: Seq[ClassDef]): Symbols = Symbols(
      this.functions,
      this.adts,
      this.classes ++ classes.map(cd => cd.id -> cd)
    )
  }
}
