/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import extraction._
import xlang.{ trees => xt }

import stainless.utils.LibraryFilter

trait Preprocessing extends oo.CachingPhase
  with IdentityFunctions
  with IdentitySorts
  with oo.IdentityClasses
  with oo.IdentityTypeDefs {

  override val s: xt.type = xt
  override val t: xt.type = xt

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override def extractSymbols(ctx: TransformerContext, symbols: s.Symbols): t.Symbols = {
    Recovery.recover(strictBVCleaner.transform(LibraryFilter.removeLibraryFlag(symbols)))
  }

}

object Preprocessing {
  def apply()(implicit ctx: inox.Context) = new {
    override val context = ctx
  } with Preprocessing
}
