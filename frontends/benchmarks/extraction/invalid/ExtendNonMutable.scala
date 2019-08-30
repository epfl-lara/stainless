// A should be annotated with @mutable
trait A

case class B(var x: BigInt) extends A {
  def f() = ()
}