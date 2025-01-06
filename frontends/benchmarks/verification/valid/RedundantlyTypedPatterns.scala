import stainless.lang._

object RedundantlyTypedPatterns {

  case class MyClass[S, T](s1: S, s2: S, t: T)

  case class MyOtherClass[S, T](s1: S, s2: S, t: T)

  case class YetAnotherClass(i1: Int, s: String, i2: Int)

  object MyOtherClass {
    def unapply[S, T](moc: MyOtherClass[S, T]): Option[(S, MyOtherClass[S, T])] = Some((moc.s1, moc))
  }


  def test1[A, B](moc: MyOtherClass[A, B]): A = moc match {
    case MyOtherClass(s1: A, MyOtherClass(s2: A, moc2: MyOtherClass[A, B])) => s1
  }

  def test2[A, B](moc: MyOtherClass[A, B]): A = moc match {
    case MyOtherClass(s1, MyOtherClass(s2, moc2)) => s1
  }

  def test3[A, B](a: A, b: B): Unit = {
    val (aa1: A, bb: B) = (a, b)
    val (aa2: A, ab1: (A, B)) = (a, (a, b))
    val (ab2: (A, B), aa3: A) = ((a, b), a)
  }

  def test4[A, B](mc: MyClass[A, B]): A = mc match {
    case MyClass(a1: A, a2: A, b: B) => a1
  }

  def test5(mc: MyClass[Int, String]): Int = mc match {
    case MyClass(a1: Int, a2: Int, b: String) => a1
  }

  def test6(yac: YetAnotherClass): Int = yac match {
    case YetAnotherClass(a1: Int, a2: String, a3: Int) => a1
  }
}