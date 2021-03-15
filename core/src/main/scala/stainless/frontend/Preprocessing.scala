/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import extraction._
import xlang.{ trees => xt }

import stainless.utils.LibraryFilter

trait Preprocessing extends inox.transformers.SymbolTransformer {

  implicit val context: inox.Context
  override val s: xt.type = xt
  override val t: xt.type = xt

  override def transform(symbols: s.Symbols): t.Symbols = {
    Recovery.recover(strictBVCleaner.transform(LibraryFilter.removeLibraryFlag(symbols)))
  }

}

object Preprocessing {
  def apply()(implicit ctx: inox.Context) = new {
    override val context = ctx
  } with Preprocessing
}
