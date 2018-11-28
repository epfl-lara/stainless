import stainless.annotation._

trait GhostCheckerNoneGet {
  @ghost
  var x: BigInt

  @ghost
  final def increment() = {
    x = x + 1
  }
}

