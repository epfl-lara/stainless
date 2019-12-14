/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen

trait LibProvider {
  import LibProvider.libPath

  protected val trees: stainless.ast.Trees

  def fun(name: String)(implicit s: trees.Symbols): trees.FunDef =
    s.lookup[trees.FunDef](libPath + name)

  def sort(name: String)(implicit s: trees.Symbols): trees.ADTSort =
    s.lookup[trees.ADTSort](libPath + name)
}

object LibProvider {
  val libPath = "stainless.wasm.Runtime."
}
