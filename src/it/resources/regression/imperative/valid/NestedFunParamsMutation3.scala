object NestedFunParamsMutation3 {

  case class Counter(var i: BigInt)  {
    def reset() = {
      i = 0
    } 
  }
  
  
  def main(c: Counter): Unit = {

    def sub(): Unit = {
      c.reset()
    } 
    sub()
    assert(c.i == 0)
  }

}

