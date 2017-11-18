/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package transformers

trait SimplifierWithPC extends TransformerWithPC with inox.transformers.SimplifierWithPC {
  import symbols._
  def pp = implicitly[PathProvider[CNFPath]]
}
