import stainless.annotation.ghost
trait ErasedCheckerNoneGet {
  erased var x: BigInt

  @ghost final def increment() = {
    x = x + 1
  }
}
