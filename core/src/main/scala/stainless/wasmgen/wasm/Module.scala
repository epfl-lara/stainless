/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package wasmgen
package wasm

import Definitions._
import Expressions.zero

// A WebAssembly module
case class Module private (
  name: Label,
  imports: Seq[Import],
  globals: Seq[Global],
  table: Table,
  data: Seq[Data],
  functions: Seq[FunDef]
)

object Module {
  def apply(name: Label, imports: Seq[Import], globals: Seq[ValDef], table: Table)
           (funGen: (GlobalsHandler, DataHandler) => Seq[FunDef]): Module = {
    val gh = new GlobalsHandler(
      globals.map(g => Global(g.name, true, zero(g.tpe)))
    )
    val dh = new DataHandler(0)
    val funs = funGen(gh, dh)

    Module(name, imports, gh.globals, table, dh.data, funs)
  }
}