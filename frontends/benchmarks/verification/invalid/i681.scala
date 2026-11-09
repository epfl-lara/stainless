object i681:

  def f(): () => Boolean =
    () => false

  def g(): Unit =
    assert(f()())
