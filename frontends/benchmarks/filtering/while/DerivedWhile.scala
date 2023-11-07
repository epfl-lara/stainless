object DerivedWhile {
  def myFunction1(x: BigInt): BigInt = {
    require(x >= 0)
    var i = 0: BigInt
    while (i < x) {
      i += 1
    }
    i
  }


  def myFunction2(x: BigInt): BigInt = {
    require(x >= 0)
    var i = 0: BigInt
    while (i < x) {
      i += 1
      while (i < x) {
        i += 1
      }
    }
    i
  }

  def myFunction3(x: BigInt): BigInt = {
    require(x >= 0)
    var i = 0: BigInt
    while (i < x) {
      i += 1
    }
    while (i < 5) {
      i += 1
    }
    i
  }
}