import stainless.lang.StaticChecks._

object RequireEnsuringMessagesStaticChecks {
  case class MyClass(a: Int) {
    require(a > 0, "a must be strictly positive")
  }

  def useMyClass(mc: MyClass): Int = {
    assert(mc.a > 0, "a is surely strictly positive")
    mc.a
  }.ensuring(_ > -42, "trivially trivial")

  def createMyClass(a: Int): MyClass = {
    require(a > 0, "To create MyClass, a must be strictly positive")
    MyClass(a)
  }
}