import stainless.lang.*
object TestContext:
  type Val = BigInt

  final case class Env(m: Map[String, Val]):
    def get(s: String) =
      m.get(s)

  def getEnv(using e: Env) = e

  type M[A] = Env ?=> A

  sealed abstract class Exp:
    def eval: M[Option[Val]] =
      this match
        case Var(s) => getEnv.get(s)
        case Plus(e1, e2) =>
          for v1 <- e1.eval
              v2 <- e2.eval
          yield v1 + v2

  final case class Var(s: String) extends Exp
  final case class Plus(e1: Exp, e2: Exp) extends Exp

end TestContext