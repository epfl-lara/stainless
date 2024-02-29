object ExportedMethods {
  object Local {
    object SimpleCounter {
      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

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

        def useCounterFromBase(y: BigInt): Unit = {
          require(y >= 0)
          x += y
          val abc = x
          add(y)
        }
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }
    object CounterWithInvariant {
      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

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

        def useCounterFromBase(y: BigInt): Unit = {
          require(y >= 0)
          x += y
          val abc = x
          add(y)
        }
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }

    object AbstractCounter {

      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

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

        def useCounterFromBase(y: BigInt): Unit = {
          require(y >= 0)
          x += y
          val abc = x
          add(y)
        }
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }

    object AbstractBaseAndCounter {

      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

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

        def useCounterFromBase(y: BigInt): Unit = {
          require(y >= 0)
          x += y
          val abc = x
          add(y)
        }
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }
  }

  object Ext {
    object SimpleCounter {
      import ExportedMethodsExt.SimpleCounter.*

      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }

    object CounterWithInvariant {
      import ExportedMethodsExt.CounterWithInvariant.*

      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }

    object AbstractCounter {
      import ExportedMethodsExt.AbstractCounter.*

      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }

    object AbstractBaseAndCounter {
      import ExportedMethodsExt.AbstractBaseAndCounter.*

      def accessExported(w: Wrapper, y: BigInt): Unit = {
        require(y >= 0)
        w.add(y)
        val abc = w.x
        w.x = y
      }

      def useCounterFromBaseOutside(b: Base, y: BigInt): Unit = {
        require(y >= 0)
        b.x += y
        val abc = b.x
        b.add(y)
      }

      case class Wrapper(base: Base) {
        export base.*

        def addWith(y: BigInt, z: BigInt): Unit = {
          require(y >= 0)
          require(z >= 0)
          x = z
          val abc = x
          add(y)
          add(z)
        }

        def parametricAddWith[T](y: BigInt, t: T): Unit = {
          require(y >= 0)
          parametricAdd(y, t)
        }
      }
    }
  }
}