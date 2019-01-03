object ExploratoryTest {


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

  def union(a: Map[Int, Int]): Map[Int, Int] = a updated (1, 2)
}