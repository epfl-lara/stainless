import stainless.lang._

object InnerClasses4 {

  abstract class Test[A] {
    def something(x: A): A
  }

  def doSomething[B](b: B, l: BigInt): Test[B] = {
    require(l > 1)

    val double = l * 2

    case class FooBarBaz[C](foo: Boolean, c: C) extends Test[B] {
      require(foo == true) // keep outer ref in Hello World

      def something(y: B): B = {

        case class HelloWorld(bar: Boolean, baz: B, ced: C) extends Test[B] {
          def something(world: B): B = {
            if (foo && bar) world else y
          }
        }

        val hello = HelloWorld(l < double, b, c)
        hello.something(y)
      }
    }

    FooBarBaz(true, "hello world")
  }

  def test = doSomething(false, 2)
}
