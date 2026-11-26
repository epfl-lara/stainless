// The verification conditions of `assert(false)`, whose condition Scala reduces to `false`, have the
// position of the assertion
object AssertFalsePosition {
  def f(x: BigInt): BigInt = {
    assert(false)
    x
  }

  def g(x: BigInt): BigInt = {
    assert(false, "unreachable")
    x
  }
}
