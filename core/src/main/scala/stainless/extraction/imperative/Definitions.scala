/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait Definitions extends innerfuns.Trees { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
      with SymbolOps
      with TypeOps { self0: Symbols =>
  }
}

