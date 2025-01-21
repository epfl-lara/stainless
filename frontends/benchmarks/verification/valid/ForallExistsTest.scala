import stainless.lang.Quantifiers.*
import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.Ensures.*
import stainless.lang.unfold
object ForallExistsTest:
  @ghost
  def forAny(x: BigInt): Unit = {
      val x4 = x + x + x + x
      val t1 = x4 + 1
      val t2 = t1 + 1
      {
        assert(x4 < t1)
        assert(x4 < t2)
        if t1 % 2 == 0 then
          assert(x4 < t1 && t1 % 2 == 0)
          ExistsThe(t1)((y: BigInt) => x4 < y && y % 2 == 0)
        else 
          assert(x4 < t2 && t2 % 2 == 0)
          ExistsThe(t2)((y: BigInt) => x4 < y && y % 2 == 0)
        ()
      }.ensuring((_:Unit) =>
         Exists((y: BigInt) => x4 < y && y % 2 == 0))
  }

  @ghost
  def exampleAE1: Unit = {
    val pNot = (x:BigInt) => !Exists((y: BigInt) => (x + x + x + x) < y && y % 2 == 0)
    val p = (x:BigInt) => Exists((y: BigInt) => (x + x + x + x) < y && y % 2 == 0)
    {
      if Exists(pNot) then
        val w: BigInt = pickWitness[BigInt](pNot)
        forAny(w)
      else
        notExistsNot(p)
    }.ensuring(_ => Forall(p))
  }

  @ghost @extern
  def pickingAny[T](f: T => Unit, property: T => Boolean): Unit = {
    require(ensures(f, (input:T, _:Unit) => property(input)))
    ()
  }.ensuring(_ => Forall(property))

  @ghost
  def exampleAE2: Unit = {
    val p = (x:BigInt) => Exists((y: BigInt) => x + x + x + x < y && y % 2 == 0)
    {
      unfold(ensures(forAny, (x:BigInt, _:Unit) => p(x)))
      assert(ensures(forAny, (x:BigInt, _:Unit) => p(x)), "stupid extensionality")
      pickingAny(forAny, p)
    }.ensuring(_ => Forall(p))
  }
