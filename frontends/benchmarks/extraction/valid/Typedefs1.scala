
object Typedefs1 {
  // Simple type alias
  type MyInt = Int

  // Also type lambdas
  type MyType[x] = x

  // Type aliases are correctly unaliased.
  def add(a: MyInt, b: MyInt): MyInt = {
    a + b
  }

  // Type lambdas are correctly evaluated and unaliased.
  def succ(a: MyType[Int]): Int = {
    require( a < 2147483647 )
    val res = a + 1
    res
  } ensuring( res => res > a)
}
