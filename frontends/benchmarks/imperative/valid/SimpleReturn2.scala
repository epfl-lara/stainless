object SimpleReturn2 {
  def example0: Int = {
    (return 50, 100)
    0
  }

  def example1: Int = {
    (50, return 100)
    assert(false)
    0
  }

  def example2: Int = {
    (return 50, return 100)
    assert(false)
    0
  }

  def example3: Int = {
    (0, 0, return 100)
    assert(false)
    0
  }

  def example4: Int = {
    (0, return 100, 0)
    assert(false)
    0
  }

  def example5: Int = {
    (return 100, 0, 0)
    assert(false)
    0
  }

  def example6: Int = {
    (return 50, return 100, 0)
    assert(false)
    0
  }

  def example7: Int = {
    (return 50, 0, return 100)
    assert(false)
    0
  }

  def example8: Int = {
    (0, return 50, return 100)
    assert(false)
    0
  }

  def example9: Int = {
    (return 50, return 100, return 200)
    assert(false)
    0
  }

  def example10(cond: Boolean): Int = {
    if (cond)
      (50, return 100, 200)
    else
      return 12
    assert(false)
    0
  }

  def tests() = {
    assert(example0 == 50)
    assert(example1 == 100)
    assert(example2 == 50)
    assert(example3 == 100)
    assert(example4 == 100)
    assert(example5 == 100)
    assert(example6 == 50)
    assert(example7 == 50)
    assert(example8 == 50)
    assert(example9 == 50)
    assert(example10(true) == 100)
    assert(example10(false) == 12)
  }
}
