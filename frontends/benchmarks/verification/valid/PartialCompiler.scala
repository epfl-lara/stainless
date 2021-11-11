import stainless.lang._
import stainless.annotation.{partialEval => _, _}
import stainless.collection._
import stainless.util.Random

object PartialCompiler {

  sealed trait Expr
  case class Var(name: String)     extends Expr
  case class Num(value: Int)       extends Expr
  case class Add(l: Expr, r: Expr) extends Expr
  case class Mul(l: Expr, r: Expr) extends Expr
  case class Rand(max: Expr)       extends Expr

  type Context = Map[String, Expr]

  @extern
  def random(max: Int): Int = 42

  case class Error(msg: String)

  def interpret(expr: Expr, ctx: Context)(fuel: Int): Either[Error, Int] = {
    require(fuel >= 0)
    decreases(fuel)

    if (fuel == 0) Left(Error("No more fuel")) else expr match {
      case Num(value) => Right(value)

      case Var(name) if ctx contains name =>
        interpret(ctx(name), ctx)(fuel - 1)

      case Var(name) =>
        Left(Error("Unbound variable: " + name))

      case Add(l, r)  => for {
        le <- interpret(l, ctx)(fuel - 1)
        re <- interpret(r, ctx)(fuel - 1)
      } yield le + re

      case Mul(l, r)  => for {
        le <- interpret(l, ctx)(fuel - 1)
        re <- interpret(r, ctx)(fuel - 1)
      } yield le * re

      case Rand(max) =>
        interpret(max, ctx)(fuel - 1).map(random(_))
    }
  }

  val program: Expr = Mul(Num(10), Add(Var("x"), Rand(Num(42))))

  def left_unbound(y: Int) = partialEval {
    val ctx: Context = Map("y" -> Num(y))
    interpret(program, ctx)(42)                                // Left(Error("Unbound variable: x"))
  } ensuring { _ == Left[Error, Int](Error("Unbound variable: x")) }

  def left_fuel(x: Int) = partialEval {
    val ctx: Context = Map("x" -> Num(x))
    interpret(program, ctx)(2)                                // Left(Error("No more fuel"))
  } ensuring { _ == Left[Error, Int](Error("No more fuel")) }

  def right(x: Int) = partialEval {
    interpret(program, Map("x" -> Num(x)))(42)                 // Right(10 * (ctx("x") + random(42)))
  } ensuring { _.isRight }

}
