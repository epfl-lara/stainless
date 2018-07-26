
object SuperAbstract {

  sealed abstract class A {
    def hello: BigInt
  }

  case class B() extends A {
    override def hello = super.hello + 1
  }

}
