/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen

/** Defines ASTs representing wasm programs.
  * The definitions correspond to the text format,
  * with labels represented as strings.
  *
  * Limitations: Not everything defined in wasm is defined here,
  * only what was required for our representation.
  */
package object wasm {
  type Label = String
}
