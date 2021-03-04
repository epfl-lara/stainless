object NestedReturn {

  def example0: Int = {
    def f: Int = {
      return 5
      assert(false)
      0
    }
    return f
    assert(false)
    0
  }

  def example1: Int = {
    def f: Int = 5
    return f
    assert(false)
    0
  }

  def example2: Int = {
    def f: Int = {
      return 5
      assert(false)
      50
    }
    f
  }

  def example3: Int = {
    def f: Int = {
      def g: Int = {
        return 10
        assert(false)
        0
      }
      return 20
      assert(false)
      100
    }
    f
  }

  def example4: Int = {
    def f: Int = {
      def g: Int = {
        return 10
        assert(false)
        100
      }
      return g
      assert(false)
      44
    }
    f
  }

  def example5(cond: Boolean): Int = {
    def f: Int = {
      def g1: Int = {
        return 10
        assert(false)
        100
      }
      def g2: Int = {
        return 30
        assert(false)
        100
      }
      if (cond) {
        return g1
        assert(false)
      }
      else
        return g2
      assert(false)
      0
    }
    f
  }

  def tests: Unit = {
    assert(example0 == 5)
    assert(example1 == 5)
    assert(example2 == 5)
    assert(example3 == 20)
    assert(example4 == 10)
    assert(example5(true) == 10)
    assert(example5(false) == 30)
  }

}
