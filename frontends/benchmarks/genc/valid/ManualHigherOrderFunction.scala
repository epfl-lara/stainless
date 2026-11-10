import stainless.annotation.*
import stainless.io.*

/** A manually defined function with a parameter whose type is a function type
 *  taking a function. GenC does not print the signatures of manually defined
 *  functions, so it accepts such types there.
 */
object ManualHigherOrderFunction:

  def inc(x: Int): Int = if x == Int.MaxValue then x else x + 1

  def callWithOne(g: Int => Int): Int = g(1)

  @cCode.function(
    code = "int32_t __FUNCTION__(int32_t (*f)(int32_t (*)(int32_t)), int32_t (*g)(int32_t)) { return f(g); }",
    headerIncludes = "",
    cIncludes = ""
  )
  def applyTo(f: (Int => Int) => Int, g: Int => Int): Int = f(g)

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    StdOut.println(applyTo((h: Int => Int) => callWithOne(h), (x: Int) => inc(x))) // 2
