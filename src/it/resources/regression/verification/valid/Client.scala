/* Copyright 2009-2016 EPFL, Lausanne */

import leon.collection._
import leon.lang._

object Minimal {

  case class Client(f: Int => List[Int])

  val client = Client(x => List(1))

  //   def f(x: Int) = List(1)
  //   val client = Client(f)

  def theorem() = {
    client.f(0).size != BigInt(0)
  } holds

}

