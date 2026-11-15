object i665:

  sealed abstract class A

  case class C() extends A

  case class Box[X](x: X) extends A

  def typeParameter[T](a: A): Boolean =
    a.isInstanceOf[T]

  def typeArgument(a: A): Boolean =
    a.isInstanceOf[Box[BigInt]]
