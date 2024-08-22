/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._
import stainless.proof._

object MonadicTry1 {

  def success(): Try[Unit] = Success[Unit](())
  def failure(): Try[Unit] = Failure[Unit](Exception("failure"))

  def checkVal(b: Boolean): Try[Unit] = {
    if (b) Success[Unit](())
    else Failure[Unit](Exception("checkVal failed"))
  }.ensuring(res => res match {
    case Success(_) => b
    case Failure(_) => !b
  })

}
