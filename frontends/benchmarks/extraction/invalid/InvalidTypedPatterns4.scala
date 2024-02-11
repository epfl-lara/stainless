object InvalidTypedPatterns4 {
  case class MyClass[S, T](s1: S, s2: S, t: T)

  def test5(mc: MyClass[Int, String]): Int = mc match {
    case MyClass(a1: Int, a2: String, b: String) => a1 // a2: String is invalid
  }
}