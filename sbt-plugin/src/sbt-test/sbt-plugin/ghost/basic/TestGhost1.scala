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

  case class Counter(var n: Int, @ghostAnnot var count: BigInt)

  def index(cs: Array[Counter]): Int = {
    require(cs.length > 0)
    touchFile("ghostReceiverEvaluated")
    0
  }.ensuring(res => 0 <= res && res < cs.length)

  def doGhostStuff(): Unit = {
    ghost {
      sneakyGhost()
      touchFile("insideGhostCalled")
    }

    @ghostAnnot var localGhost = sneakyGhost()

    localGhost = ghostParam1(sneakyGhost(), BigInt(20))

    val c = Counter(0, 0)
    c.count = sneakyGhost() // the right-hand side of a ghost field assignment is not evaluated

    val cs = Array(Counter(1, 0))
    cs(index(cs)).count = sneakyGhost() // neither is its receiver
  }
}
