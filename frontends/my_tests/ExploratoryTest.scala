object ExploratoryTest {


  def bar(n : Set[(Int, Int)]): Set[Int] = {
    val n = n + (1, 1)
    n + 1
  }

//  def foo(baz: Int): Int = baz match {
//    case a @ 1  => 1 + 2
//    case 42 => baz
//    case (a, b) => a
//  }
}