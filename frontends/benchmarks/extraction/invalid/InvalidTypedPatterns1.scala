import stainless.lang._

object InvalidTypedPatterns1 {

  case class MyOtherClass[S, T](s1: S, s2: S, t: T)

  object MyOtherClass {
    def unapply[S, T](moc: MyOtherClass[S, T]): Option[(S, MyOtherClass[S, T])] = Some((moc.s1, moc))
  }


  def test[A, B](moc: MyOtherClass[A, B]): A = moc match {
    case MyOtherClass(s1: A, MyOtherClass(s2: B, moc2: MyOtherClass[A, B])) => s1 // s2: B is invalid
  }
}