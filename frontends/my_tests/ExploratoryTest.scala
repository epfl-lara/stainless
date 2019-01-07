object ExploratoryTest {

//  def matching(a: Int): String = a match {
//    case 1 => "First"
//    case 2 => "Second"
//    case _ if a < 5 => "Third"
//    case _ => "Rest"
//  }


//  def first(a: Int, b: Int): Int = a + b
//
//  def first(a: String, b: String): Int = 1
//
//  def test() = {
//    val a = 1
//    val b = 2
//    first(a, b)
//  }
//
//  def tesint(): String = {
//    val first = "Stevan"
//    val second = " Ognjanovic"
//    first + second
//  }
//
//  def check() = {
//    val f1 = (x: Int) => x + 1             // simple anonymous function
//    val y  = 2
//    val f2 = (x: Int) => f1(x) + y             // closes over `f1` and `y`
//    val f3 = (x: Int) => if (x < 0) f1 else f2
//  }
//
//  def first(a: Set[Int], b: Int) = {
//    a + b
//  }
//
//  def second(a: Int, b: Int) = {
//    a + b
//  }
//
//  def third(a: Map[Int, String], b: Int, c: String) = {
//    a + (b -> c)
//  }

//  def max(x: Int, y: Int): Int = {
//    require(0 <= x && 0 <= y)
//    val d = x - y
//    if (d > 0) x
//    else y
//  }
//
//  def calling(): Int = {
//    max(1, 2)
//  }
//  def foo1(x: Int): Int = {
//    x match {
//      case 1 => 2
//    }
//  }

//  def fib1(n: Int): Int = n match {
//    case 0 => n
//    case 1 => n
//    case _ => fib1(n - 1) + fib1(n - 2)
//  }
//
//  def factorial(n: Int): Int = {
//    if (n == 0)
//      1
//    else
//      n * factorial(n-1)
//  }

//  def test(x: Short, y: Short): Short = x * y

//  def test(a: Int, b: Int): Int = {
//    require(b > 0)
//    a / b
//  }

  //  def bar[T](n: Map[T, T], elem: (T, T)): Map[T, T] = {
  //    n + elem
  //  }


  //  def test(): Map[Int, Int] = {
  //    bar(new Map[Int, Int](), (1, 2))
  //  }

  //  def test1(): Set[Int] = {
  //    Set[Int]()
  //  }
  //
  //  def test2(): () => Set[Int] = {
  //    test1
  //  }

  //  def foo(baz: Int): Int = baz match {
  //    case a @ 1  => 1 + 2
  //    case 42 => baz
  //    case (a, b) => a
  //  }

  //  def test3[A, B]: Unit = ()
  //
  //
  //  def test[A, B](first: A, second: B): (A, B) = (first, second)

//  // first
//  def fun[B](a: String, b: B): (B, String) = (b, a)
//  // second
//  def fun(a: Int, b: Int): (Int, Int) = (a, b)
//  // third
//  def fun(a: Int, b: Char): (Char, Int) = (b, a)
//
//  def calls()= {
//    fun(1, 2)         // elaborated to second
//    fun(1, 'b')       // elaborated to third
//    fun("Foo", "Bar") // elaborated to first
//  }
  //
  //  def main(): Unit = {
  //    call()
  //    ()
  //    print(call())
  //}

  def setCreation() = {
    val set = Set(1, 2, 3)
    val set2 = Set(1, 2)
    set ++ set2
  }

  //  def union(a: Map[Int, Int]): Map[Int, Int] = a updated (1, 2)
}