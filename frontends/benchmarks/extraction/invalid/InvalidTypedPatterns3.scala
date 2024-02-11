object InvalidTypedPatterns3 {
  case class MyClass[S, T](s1: S, s2: S, t: T)

  def test[A, B](mc: MyClass[A, B]): A = mc match {
    case MyClass(a1: A, a2: B, b: B) => a1 // a2: B is invalid
  }
}