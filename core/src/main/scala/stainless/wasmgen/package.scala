/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

/** Provides code to translate stainless ASTs to WebAssembly code.
  *
  * The strategy followed is to first translate to an intermediate language
  * which extends stainless trees (see [[stainless.wasmgen.intermediate]])
  * and then generate WebAssembly.
  *
  * A partial modelling of the WebAssembly language is provided under
  * [[stainless.wasmgen.wasm]].
  *
  * The translation from intermediate trees to WebAssembly is under [[stainless.wasmgen.codegen]].
  * The current implementation uses linear memory to implement heap operations,
  * but it is designed to easily incorporate reference types once they become available.
  * See [[stainless.wasmgen.codegen.CodeGeneration]].
  *
  * Current limitations:
  * * BigInts and Reals are represented as i64 and f64 respectively.
  * * Forall and Choose are not implemented.
  * * Maps, Sets and Bags have very basic and computationally inefficient implementations.
  */
package object wasmgen