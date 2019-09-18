/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait Definitions extends oo.Trees { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
      with SymbolOps
      with TypeOps { self0: Symbols =>
  }
}

