object ExportedMethodsExt {

  // This object is used for the other ExportedMethods
  // but we need to have at least one invalid VC to pass the "invalid" test suite
  def dummyInvalid(x: BigInt): Unit = {
    assert(x == 0)
  }

  object SimpleCounter {
    case class Counter(var x: BigInt) {
      def add(y: BigInt): Unit = {
        require(y >= 0)
        x += y
      }

      def parametricAdd[T](y: BigInt, t: T): Unit = {
        require(y >= 0)
        x += y
      }
    }

    case class Base(cnt: Counter) {
      export cnt.*
    }
  }

  object CounterWithInvariant {
    case class Counter(var x: BigInt) {
      require(x >= 0)

      def add(y: BigInt): Unit = {
        require(y >= 0)
        x += y
      }

      def parametricAdd[T](y: BigInt, t: T): Unit = {
        require(y >= 0)
        x += y
      }
    }

    case class Base(cnt: Counter) {
      export cnt.*
    }
  }

  object AbstractCounter {
    abstract case class Counter() {
      var x: BigInt

      def add(y: BigInt): Unit = {
        require(y >= 0)
        x += y
      }

      def parametricAdd[T](y: BigInt, t: T): Unit = {
        require(y >= 0)
        x += y
      }
    }

    case class Base(cnt: Counter) {
      export cnt.*
    }
  }

  object AbstractBaseAndCounter {
    abstract case class Counter() {
      var x: BigInt

      def add(y: BigInt): Unit = {
        require(y >= 0)
        x += y
      }

      def parametricAdd[T](y: BigInt, t: T): Unit = {
        require(y >= 0)
        x += y
      }
    }

    abstract case class Base() {
      val cnt: Counter
      export cnt.*
    }
  }
}