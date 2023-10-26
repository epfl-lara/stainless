/** Author: Samuel Chassot
 * 
 * Cell class
 * 
 * Used to provide better handling of mutable state
 **/

package stainless.lang

import stainless.annotation._


@library
case class Cell[@mutable T](var v: T) 