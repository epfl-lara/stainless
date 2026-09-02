object OpaqueTypesRefinements {
  opaque type UInt32 = {v: BigInt with v >= 0 && v <= BigInt(0xFFFFFFFFL)}
  object UInt32 {
    def apply(v: BigInt with v >= 0 && v <= BigInt(0xFFFFFFFFL)): UInt32 = v
  }
  extension (v: UInt32)
    def foo(other: UInt32 with v + other <= BigInt(0xFFFFFFFFL)): UInt32 = v + other
}

// Regression test for the "Unsupported call to + on v$N" extraction error:
// at the call site below, the qualifier of `foo`'s parameter is instantiated
// outside the defining scope of the opaque type, where `+` is dispatched on a
// receiver whose type is the opaque alias. Extraction must resolve the alias
// to its translucent super type for the dispatch to succeed.
object OpaqueTypesRefinementsUse {
  import OpaqueTypesRefinements.*
  def test(): Unit = {
    UInt32(BigInt(123)).foo(UInt32(BigInt(123)))
    ()
  }
}
