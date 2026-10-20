import stainless.lang._

// A package object with an opaque type alias: members called through an explicit
// `this` are inlined as `package$_this.helper(x)`.
package object opaqueTypesInline4 {
  opaque type Id[A] = A

  def helper(b: BigInt): BigInt = b

  inline def viaThis(value: BigInt): BigInt = this.helper(value)
  inline def plain(value: BigInt): BigInt = helper(value)
}

object OpaqueTypesInline4 {
  def run(x: BigInt): BigInt = {
    opaqueTypesInline4.viaThis(x) + opaqueTypesInline4.plain(x)
  }.ensuring(_ == x + x)
}
