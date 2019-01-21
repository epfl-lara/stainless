object ExploratoryTest {


  def first(a: Set[Int], b: Int) = { // inferred type Set[Int]
    a + b // elaborated to SetAdd
  }

  def second(a: Int, b: Int) = { // inferred result is Int
    a + b // elaborated to primitive addition
  }
//
  def third(a: Map[Int, String], b: Int, c: String) = { // inferred type is Map[Int, String]
    a + (b -> c) // elaborated to MapUpdated
  }

  // first
  def fun[B](a: String, b: B): (B, String) = (b, a)

  // second
  def fun(a: Int, b: Int): (Int, Int) = (a, b)

  // third
  def fun(a: Int, b: Char): (Char, Int) = (b, a)

  def calls() = {
    fun(1, 2) // elaborated to second
    fun(1, 'b') // elaborated to third
    fun("Foo", "Bar") // elaborated to first
  }

  def matching(a: Int): String = a match {
    case 1 => "First"
    case 2 => "Second"
    case _ if a < 5 => "Third"
    case _ => "Rest"
  }

  def check() = {
    val f1 = (x: Int) => x + 1 // simple anonymous function
    val y = 2
    val f2 = (x: Int) => f1(x) + y // closes over `f1` and `y`
    val f3 = (x: Int) => if (x < 0) f1 else f2
  }


  //   no verification executed
  def test(a: Int): Boolean = {
    val b = a > 3
    b
  }

  // counter example on input value 3
  def test(a: Int): Boolean = {
    val b = a > 3
    assert(b == true)
    b
  }

  // counter example on input value 4
  def test(a: Int): Boolean = {
    val b = a == 4
    b
  }.holds

  //   counter example on input value 5
  def test(a: Int): Boolean = {
    val b = a != 5
    b
  } ensuring { res => res == true }

  //passes verification because of require
  def test(a: Int): Boolean = {
    require(a > 3)
    val b = a > 3
    b
  } ensuring { res => res == true }
}