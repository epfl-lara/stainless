object TargetMutation8 {

  case class A(var i: BigInt)
  case class B(arr: Array[A])
  case class C(a: A, b: B)

  def createA(i: BigInt, counter: A): A = {
    counter.i += 1
    A(i)
  }

  def test(n: BigInt, counter: A): C = {
    val origCount = counter.i
    // This triggers AntiAliasing 2nd case for Let binding of mutable types
    // *without* triggering EffectsChecker#check#traverser#traverse#Let
    // because:
    // -`b` is bound to a fresh expression (passes EffectsChecker#check#traverser#traverse#Let check)
    // -the transformation of `b` produces an expression whose target cannot be computed
    // -there are no sharing between the terminal variables of `b` and the rest of the body
    val b = {
      if (n > 0) {
        val b = B(Array.fill(5)(A(0)))
        b.arr(0) = createA(1, counter)
        b
      } else B(Array.fill(5)(A(0)))
    }
    val a = createA(2, counter)
    assert(n <= 0 || counter.i == origCount + 2)
    assert(n > 0 || counter.i == origCount + 1)
    C(a, b)
  }
}