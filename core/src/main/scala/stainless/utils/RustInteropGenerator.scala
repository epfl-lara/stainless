/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package utils

import scala.reflect.runtime.universe._
import inox.utils.{RustInteropGeneration, RustInteropGenerator}

object RustInteropGeneratorTool extends inox.utils.RustInteropGenerator {
  override protected val serializer: RustInteropGeneration =
    new XLangSerializer(stainless.extraction.xlang.trees) with RustInteropGeneration {
      override protected val optSymbolIdentifierT: Option[Type] =
        Some(typeOf[stainless.ast.SymbolIdentifier])
      override protected val optPatternT: Option[Type] =
        Some(typeOf[stainless.trees.Pattern])
    }
}
