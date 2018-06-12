
import stainless.lang._

object InnerClassesMut {

  abstract class Bar {
    def hello: BigInt
  }

  def bar: BigInt = {
    case class Stuff(var world: BigInt) extends Bar {
      def hello: BigInt = Some(BigInt(42) + world).get
    }

    val s: Stuff = Stuff(90)
    s.world += 10
    s.hello
  }

  def test = {
    bar == BigInt(142)
  }.holds
}
