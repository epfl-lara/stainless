object ExploratoryTest {


  def bar(n: Set[Int]): Set[Set[Int]] = {
    val x: Set[Int] = Set(1)
    n + x
  }

//  def foo(baz: Int): Int = baz match {
//    case a @ 1  => 1 + 2
//    case 42 => baz
//    case (a, b) => a
//  }
}