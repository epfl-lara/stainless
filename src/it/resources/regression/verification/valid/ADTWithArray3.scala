/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

/*
 * Not sure what is wrong there, but the ArrayEncoding used to
 * crash on this specific combination of nested function with
 * transitive requirements to length of buffer in Kernel.
 */
object ADTWithArray3 {

  case class Kernel(size: Int, buffer: Array[Int])

  def isKernelValid(kernel: Kernel): Boolean = kernel.buffer.length == kernel.size * kernel.size

  def applyFilter(kernel: Kernel): Int = {
    require(isKernelValid(kernel))
    12
  }

  def testFilterConvolutionSmooth: Boolean = {
    val smoothed = Array(124, 158, 76, 73)
    val kernel = Kernel(3, Array(1, 1, 1,
                                 1, 2, 1,
                                 1, 1, 1))

    def nested(): Unit = {
      require(smoothed.length > 0)
      smoothed(0) = applyFilter(kernel)
    }
    nested()
    
    smoothed(0) >= 0
  }
}
