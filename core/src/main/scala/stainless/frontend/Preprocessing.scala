/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import extraction._
import xlang.{ trees => xt }

import stainless.utils.LibraryFilter

class Preprocessing private(override val s: xt.type, override val t: xt.type)
                           (using val context: inox.Context)
  extends inox.transformers.SymbolTransformer {

  def this()(using inox.Context) = this(xt, xt)

  override def transform(symbols: s.Symbols): t.Symbols = {
    Recovery.recover(strictBVCleaner.transform(LibraryFilter.removeLibraryFlag(symbols)))
  }
}
