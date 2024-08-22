object i1343a {
  def myLemma(x: BigInt): Unit = {
    ()
 }.ensuring(_ => x + x == 2 * x)

  def ok1(x: BigInt): Unit = {
    require {
      myLemma(x)
      x >= 0
    }
    assert(x >= 0)
  }

  def ok2(x: BigInt): Unit = {
    require {
      val y = x + 2
      myLemma(x)
      x >= 0
    }
    assert(x >= 0)
  }

  def ok3(x: BigInt): Unit = {
    require {
      val y = {
        val z = x + 3
        z + 2
      }
      myLemma(x)
      x >= 0
    }
    assert(x >= 0)
  }

  def ok4(x: BigInt): Unit = {
    require {
      val y = {
        val z = x + 3
        z + 2
      }
      myLemma(x)
      val w = y + 2
      y >= 0
    }
    assert(x >= -5)
  }
}
