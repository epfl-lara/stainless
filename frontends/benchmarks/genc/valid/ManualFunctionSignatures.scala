import stainless.annotation.*
import stainless.io.*

/** Manually defined functions whose signatures have more parentheses than those
 *  of the parameter list. GenC declares such a function with the part of its
 *  code that precedes its body.
 */
object ManualFunctionSignatures:

  def inc(x: Int): Int = if x == Int.MaxValue then x else x + 1

  def dec(x: Int): Int = if x == Int.MinValue then x else x - 1

  /** The parameter list contains the parentheses of a function pointer. */
  @cCode.function(
    code = "int32_t __FUNCTION__(int32_t (*f)(int32_t), int32_t x) { return f(x); }",
    headerIncludes = "",
    cIncludes = ""
  )
  def applyTo(f: Int => Int, x: Int): Int = f(x)

  /** The parameter list is not the first parenthesis of the signature. */
  @cCode.function(
    code = """
      |int32_t (*__FUNCTION__(bool first, int32_t (*f)(int32_t), int32_t (*g)(int32_t)))(int32_t) {
      |  return first ? f : g;
      |}
      |""",
    headerIncludes = "",
    cIncludes = ""
  )
  def choose(first: Boolean, f: Int => Int, g: Int => Int): Int => Int = if first then f else g

  /** The comments have parentheses, braces and quotes, and the last one would
   *  hide what follows the signature in the declaration.
   */
  @cCode.function(
    code = """
      |/* Not the body: { ) " ' */
      |int32_t __FUNCTION__(int32_t x) // nor here: { ( " '
      |{
      |  return x == INT32_MIN ? x : -x;
      |}
      |""",
    headerIncludes = "",
    cIncludes = ""
  )
  def negate(x: Int): Int = if x == Int.MinValue then x else -x

  @cCode.`export`
  def main(): Unit =
    @ghost implicit val state: State = newState
    StdOut.println(applyTo((x: Int) => inc(x), 1)) // 2
    val up: Int => Int = choose(true, (x: Int) => inc(x), (x: Int) => dec(x))
    val down: Int => Int = choose(false, (x: Int) => inc(x), (x: Int) => dec(x))
    StdOut.println(up(1)) // 2
    StdOut.println(down(1)) // 0
    StdOut.println(negate(42)) // -42
