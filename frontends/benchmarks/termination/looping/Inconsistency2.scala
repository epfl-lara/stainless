object Inconsistency2 {
  def looping1(): () => Boolean = { () =>
    require(true)
    !looping2()()
  }

  def looping2(): () => Boolean = { () =>
    require(true)
    looping1()()
  }

  //  a()() reduces to !b()() which reduces to !a()()
  def theorem() = {
    assert(looping1()() == !looping2()())
    assert(false)
  }
}
