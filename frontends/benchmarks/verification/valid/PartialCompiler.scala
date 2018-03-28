// Disabled until we add a mode which strips all
// assertions + Either monad

// import stainless.lang._
// import stainless.annotation._
// import stainless.collection._
// import stainless.util.Random

// // Temporarily needed for map and flatMap
// object either {

//   sealed abstract class Either[A, B] {
//     def isLeft: Boolean
//     def isRight: Boolean
//     def swap: Either[B,A]

//     def map[C](f: B => C): Either[A, C] = this match {
//       case Left(a)  => Left(a)
//       case Right(b) => Right(f(b))
//     }

//     def flatMap[C](f: B => Either[A, C]): Either[A, C] = this match {
//       case Left(a)  => Left(a)
//       case Right(b) => f(b)
//     }

//     def get: B = {
//       require(isRight)
//       val Right(value) = this
//       value
//     }
//   }

//   case class Left[A,B](content: A) extends Either[A,B] {
//     def isLeft  = true
//     def isRight = false
//     def swap    = Right[B, A](content)
//   }

//   case class Right[A,B](content: B) extends Either[A,B] {
//     def isLeft  = false
//     def isRight = true
//     def swap    = Left[B, A](content)
//   }

// }

// object comp {

//   import either._

//   sealed trait Expr
//   case class Var(name: String)     extends Expr
//   case class Num(value: Int)       extends Expr
//   case class Add(l: Expr, r: Expr) extends Expr
//   case class Mul(l: Expr, r: Expr) extends Expr
//   case class Rand(max: Expr)       extends Expr

//   type Context = Map[String, Expr]

//   @extern
//   def random(max: Int): Int = {
//     Random.nativeNextInt(max)(42)
//   }

//   case class Error(msg: String)

//   def interpret(expr: Expr, ctx: Context)(fuel: Int): Either[Error, Int] = {
//     require(fuel >= 0)
//     decreases(fuel)

//     if (fuel == 0) Left(Error("No more fuel")) else expr match {
//       case Num(value) => Right(value)

//       case Var(name) if ctx contains name =>
//         interpret(ctx(name), ctx)(fuel - 1)

//       case Var(name) =>
//         Left(Error("Unbound variable: " + name))

//       case Add(l, r)  => for {
//         le <- interpret(l, ctx)(fuel - 1)
//         re <- interpret(r, ctx)(fuel - 1)
//       } yield le + re

//       case Mul(l, r)  => for {
//         le <- interpret(l, ctx)(fuel - 1)
//         re <- interpret(r, ctx)(fuel - 1)
//       } yield le * re

//       case Rand(max) =>
//         interpret(max, ctx)(fuel - 1).map(random(_))
//     }
//   }

//   val program: Expr = Mul(Num(10), Add(Var("x"), Rand(Num(42))))

//   // @partialEval
//   def unknown(ctx: Context) = {
//     require(ctx contains "x")
//     interpret(program, ctx)(42)
//   }

//   // @partialEval
//   def left_unbound(y: Int) = {
//     val ctx: Context = Map("y" -> Num(y))
//     interpret(program, ctx)(42)                                // Left(Error("Unbound variable: x"))
//   } ensuring { _ == Left[Error, Int](Error("Unbound variable: x")) }

//   // @partialEval
//   def left_fuel(x: Int) = {
//     val ctx: Context = Map("x" -> Num(x))
//     interpret(program, ctx)(2)                                // Left(Error("No more fuel"))
//   } ensuring { _ == Left[Error, Int](Error("No more fuel")) }

//   // @partialEval
//   def right(x: Int) = {
//     interpret(program, Map("x" -> Num(x)))(42)                 // Right(10 * (ctx("x") + random(42)))
//   } ensuring { _ == Right[Error, Int](10 * (x + random(42))) }

// }
