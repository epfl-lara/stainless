/** Author: Samuel Chassot
 * 
 * Cell class
 * 
 * Used to provide better handling of mutable state
 **/

package stainless.lang

import stainless.annotation._


@library
case class Cell[@mutable T](var v: T) {
    @ignore @library
    def swap(other: Cell[T]): Unit = {
      val t = other.v
      other.v = v
      this.v = t
  }
}