import stainless.lang._

// An opaque type constructor (its alias is a type lambda), and an inline method
// taking a lambda whose type mentions a class of the object, plus a by-name argument.
object OpaqueTypesInline3 {
  object Lib {
    opaque type Id[A] = A

    case class Box[A](a: A)

    def helper(b: BigInt): BigInt = b

    inline def apply[A](b: Box[A])(f: Box[A] => BigInt)(inline g: => BigInt): BigInt =
      f(b) + g + helper(1)
  }

  def run(b: Lib.Box[BigInt]): BigInt = {
    Lib(b)(bb => bb.a)(2)
  }.ensuring(_ == b.a + 3)
}
