object ADTInitialization2 {

  object A {
    case class Positive(value: BigInt = 0) {
      require(value >= 0)
    }
  }

  object B {
    case class Positive(value: BigInt = 100) {
      require(value > 0)
    }
  }

}
