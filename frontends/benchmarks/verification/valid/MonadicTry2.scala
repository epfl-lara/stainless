/* Copyright 2009-2024 EPFL, Lausanne */

import stainless.lang._
import stainless.proof._

object MonadicTry2 {

  def checkPositive(i: BigInt): Try[BigInt]= {
    if (i > 0) Success[BigInt](i)
    else Failure[BigInt](Exception("i is not positive"))
  } ensuring(res => res match {
    case Success(ii) => i > 0 && i == ii
    case Failure(_) => i <= 0
  })

  def checkEven(i: BigInt): Try[BigInt] = {
    if (i % 2 == 0) Success[BigInt](i)
    else Failure[BigInt](Exception("i is not even"))
  } ensuring(res => res match {
    case Success(ii) => i % 2 == 0 && i == ii
    case Failure(_) => i % 2 != 0
  })

  def checkEvenPositive(i: BigInt): Try[BigInt] = {
    checkPositive(i).flatMap(ii => checkEven(ii))
  } ensuring(res => res match {
    case Success(ii) => i > 0 && i % 2 == 0 && i == ii
    case Failure(_) => i <= 0 || i % 2 != 0
  })

  def evenPlusOne(i: BigInt): Try[BigInt] = {
    checkEven(i).flatMap(ii => checkPositive(ii)).map(ii => ii + 1)
  } ensuring(res => res match {
    case Success(ii) => i % 2 == 0 && i > 0 && ii == i  + 1  && ii % 2 == 1
    case Failure(_) => i % 2 != 0 || i <= 0
  })

}
