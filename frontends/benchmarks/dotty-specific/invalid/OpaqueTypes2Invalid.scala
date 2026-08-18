object OpaqueTypes2Invalid {
  opaque type Positive <: BigInt = BigInt
  object Positive {
    def apply(b: BigInt): Positive = {
      require(b >= 0)
      b
    }
  }
}

// Guards against the precondition VC silently disappearing: when the bounded
// opaque type is extracted as an abstract type instead of an alias, the type
// encoding boxes `apply`'s body and swallows its `require`, making this call
// verify vacuously. Extracting the alias keeps the precondition, so this
// violating call must be reported as invalid.
object OpaqueTypes2InvalidUse {
  import OpaqueTypes2Invalid.*
  def bad: BigInt = Positive(BigInt(-1))
}
