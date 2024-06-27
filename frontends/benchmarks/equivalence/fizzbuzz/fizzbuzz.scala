import stainless.collection.*

object FizzBuzz:

  sealed trait Outcome
  case class Fizz() extends Outcome
  case class Buzz() extends Outcome
  case class FizzBuzz() extends Outcome
  case class Number(n: BigInt) extends Outcome

  def response1(n: BigInt): Outcome =
    if n % 5 == 0 then
      if n % 3 == 0 then FizzBuzz()
      else Buzz()
    else if n % 3 == 0 then Fizz()
    else Number(n)

  def ordinalSeq1(to: BigInt): List[BigInt] =
    require(0 <= to)
    if to == 0 then List[BigInt]()
    else
      Cons(to, ordinalSeq1(to - 1))

  def fizzBuzz1(to: BigInt): List[Outcome] =
    require(0 <= to)
    ordinalSeq1(to).map(response1)

  def fizzBuzz2(to: BigInt): List[Outcome] =
    require(0 <= to)
    if to == 0 then List[Outcome]()
    else
      if to % 15 == 0 then Cons(FizzBuzz(), fizzBuzz2(to - 1))
      else
        if to % 3 == 0 then Cons(Fizz(), fizzBuzz2(to - 1))
        else
          if to % 5 == 0 then Cons(Buzz(), fizzBuzz2(to - 1))
          else Cons(Number(to), fizzBuzz2(to - 1))