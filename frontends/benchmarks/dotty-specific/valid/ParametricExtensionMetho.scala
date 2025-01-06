object ParametricExtensionMetho {
  sealed trait Opt[+T]
  case object Non extends Opt[Nothing] // Where is Oui?
  final case class Som[+T](content: T) extends Opt[T]

  extension[T](m: Opt[T])
    def flatMap[U](f: T => Opt[U]): Opt[U] =
      m match
        case Non => Non
        case Som(t) => f(t)

  def test[A, B](a: A, f: A => B): Unit =
    assert(Som(a).flatMap(a => Som(f(a))) == Som(f(a)))
    assert(Som(a).flatMap(_ => Non) == Non)
    assert((Non : Opt[A]).flatMap(a => Som(f(a))) == Non)
}