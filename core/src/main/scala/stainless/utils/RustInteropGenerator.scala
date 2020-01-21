/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package utils

import inox.utils.{RustInteropGeneration, RustInteropGenerator}

object RustInteropGeneratorTool extends inox.utils.RustInteropGenerator {
  override protected val serializer: RustInteropGeneration =
    new XLangSerializer(stainless.extraction.xlang.trees) with RustInteropGeneration
}
