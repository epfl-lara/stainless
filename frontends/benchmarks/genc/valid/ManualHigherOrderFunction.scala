import stainless.annotation.*
import stainless.io.*

/** A manually defined function with a parameter whose type is a function type
 *  taking a function. GenC does not print the signatures of manually defined
 *  functions, so it accepts such types there. The C code takes the functions as
 *  `void*`, as the declaration that GenC extracts from it ends at its first
 *  closing parenthesis.
 */
object ManualHigherOrderFunction:

  def inc(x: Int): Int = if x == Int.MaxValue then x else x + 1

  def callWithOne(g: Int => Int): Int = g(1)

  @cCode.function(
    code =
      "int32_t __FUNCTION__(void* f, void* g) { return ((int32_t (*)(int32_t (*)(int32_t))) f)((int32_t (*)(int32_t)) g); }",
    headerIncludes = "",
    cIncludes = ""
  )
  def applyTo(f: (Int => Int) => Int, g: Int => Int): Int = f(g)

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    StdOut.println(applyTo((h: Int => Int) => callWithOne(h), (x: Int) => inc(x))) // 2
