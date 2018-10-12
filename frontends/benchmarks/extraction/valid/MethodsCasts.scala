object bug {

  abstract class Cap[S] {
    def init: Fig[Unit, S]
  }

  case class Foo()
  case class Fig[A, B]()

  case object Tak extends Cap[Foo] {
    def init: Fig[Unit, Foo] = Fig[Unit, Foo]()
  }
}
