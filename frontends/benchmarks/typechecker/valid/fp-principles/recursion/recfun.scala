/* Copyright 2017- LARA, EPFL, Lausanne.
   Author: Dragana Milovancevic. */
package recfun

import stainless.lang._
import stainless.collection._

object Main {
  // Exercise 1
  def pascal(c: BigInt, r: BigInt): BigInt = {
    require(c>=0 && r>=0 && c<=r)
    decreases(r)
    if(c==0) 1
    else if(r==c) 1
    else pascal(c-1, r-1) + pascal(c, r-1)
  }

  def checkPascal(c: BigInt): Boolean = {
    c<0 || pascal(c, c) == 1
  } holds

  def checkPascal2(c: BigInt, r: BigInt): Boolean = {
    require(c>=0 && r>=0 && c<=r)
    pascal(c,r)==1 || pascal(c,r) == pascal(c-1,r-1) + pascal(c,r-1)
  } holds

  // Exercise 2
  def balance(chars: List[Char]): Boolean = {
     def recbalance(chars: List[Char], n: BigInt) : Boolean = {
       decreases(chars)
       if (n < 0) false
       else if (chars.isEmpty) {
        if (n == 0) true
        else false
       }
       else if (chars.head == '(') recbalance(chars.tail, n+1)
       else if (chars.head == ')') recbalance(chars.tail, n-1)
       else recbalance(chars.tail, n)
     }
     recbalance(chars, 0)
  }

  def checkBalance(chars: List[Char]) : Boolean = {
    !balance(')' :: chars)
  } holds

  // Exercise 3
  def distinct[T](l: List[T]): Boolean = {
    decreases(l)
    l match {
      case Nil() => true
      case Cons(x,xs) => !xs.contains(x) && distinct(xs)
    }
  }

  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  def countChange(money: BigInt, coins: List[BigInt]): BigInt = {
    require(coins.forall(_ > 0) && distinct(coins))
    decreases(max(0, money), coins)

    if (money == 0) BigInt(1)
    else if (money < 0 || coins.isEmpty) BigInt(0)
    else countChange(money-coins.head, coins) + countChange(money, coins.tail)
  } ensuring(_ >= 0)
}
