object ExploratoryTest {


  def tesint(): String = {
    val first = "Stevan"
    val second = " Ognjanovic"
    first + second
  }

//  def check(): Unit = {
//    val f1 = (x: Int) => x + 1             // simple anonymous function
//    val y  = 2
//    val f2 = (x: Int) => f1(x) + y             // closes over `f1` and `y`
//    val f3 = (x: Int) => if (x < 0) f1 else f2
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

  //  def second[T, B](a: T, b: B): (B, T) = (b, a)
  //
  //  def call2(): (Char, Int) = {
  //    second(2, 'a')
  //  }
  //
  //  def second(a: Int, b: Int): (Int, Int) = (a, b)
  //
  //  def second(a: Int, b: Char): (Char, Int) = (b, a)
  //
  //  def call(): (Int, Int) = {
  //    second(2, 2)
  //  }
  //
  //  def call1(): (Char, Int) = {
  //    second(2, 'a')
  //  }
  //
  //  def main(): Unit = {
  //    call()
  //    ()
  //    print(call())
  //}

  //  def union(a: Map[Int, Int]): Map[Int, Int] = a updated (1, 2)
}