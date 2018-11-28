
import stainless.lang._

object EitherLaws {

  object FunctorLaws {

    def functorLawId[A, B](e: Either[A, B]): Boolean = {
      e.map(x => x) == e
    } holds

    def functorLawCompose[A, B, C, D](e: Either[A, B], f: B => C, g: C => D): Boolean = {
      e.map(x => g(f(x))) == e.map(f).map(g)
    } holds

  }

  object MonadLaws {

    def monadLawIdLeft[A, B](x: B, f: B => Either[A, B]): Boolean = {
      Right(x).flatMap(f) == f(x)
    } holds

    def monadLawIdRight[A, B](e: Either[A, B]): Boolean = {
      e.flatMap(Right(_)) == e
    } holds

    def monadLawAssoc[A, B, C, D](e: Either[A, B], f: B => Either[A, C], g: C => Either[A, D]): Boolean = {
      e.flatMap(f).flatMap(g) == e.flatMap(x => f(x).flatMap(g))
    } holds

  }

}
