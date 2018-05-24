import stainless.lang._

object InnerClasses1 {

  abstract class Bar {
    def hello: BigInt
  }

  def bar: BigInt = {
    case class Stuff() extends Bar {
      def hello: BigInt = Some(BigInt(42)).get
    }

    val s: Stuff = Stuff()

    s.hello
  }

  def test = {
    bar == BigInt(42)
  }.holds
}
