package test

import stainless._
import stainless.lang._
import stainless.annotation.{ghost => ghostAnnot, _}

import java.io.File

object Main {

  @extern
  def touchFile(name: String): Unit = {
    val f = new File(s"target/$name")
    f.delete() // in case it's a leftover
    f.createNewFile()
  }

  def main(args: Array[String]): Unit = {
    doGhostStuff()
  }

  @ghostAnnot def sneakyGhost(): BigInt = {
    touchFile("sneakyGhostCalled")
    BigInt(0)
  }

  def ghostParam1(@ghostAnnot x: BigInt, y: BigInt) = { BigInt(0) }

  def doGhostStuff(): Unit = {
    ghost {
      sneakyGhost()
      touchFile("insideGhostCalled")
    }

    @ghostAnnot var localGhost = sneakyGhost()

    localGhost = ghostParam1(sneakyGhost(), BigInt(20))
  }
}
