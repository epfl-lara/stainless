package test

import stainless._
import stainless.lang._
import stainless.annotation._

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

  @ghost def sneakyGhost(): BigInt = {
    touchFile("sneakyGhostCalled")
    BigInt(0)
  }

  def ghostParam1(@ghost x: BigInt, y: BigInt) = { BigInt(0) }

  def doGhostStuff(): Unit = {
    ghost {
      sneakyGhost()
      touchFile("insideGhostCalled")
    }

    @ghost var localGhost = sneakyGhost()

    localGhost = ghostParam1(sneakyGhost(), BigInt(20))
  }
}
