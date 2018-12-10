object ExploratoryTest {


  def bar(n : Map[Int, Int]): Map[Int, Int] = {
    val n = n + (1, 1)
    n + (2, 1)
  }

//  def foo(baz: Int): Int = baz match {
//    case a @ 1  => 1 + 2
//    case 42 => baz
//    case (a, b) => a
//  }
}