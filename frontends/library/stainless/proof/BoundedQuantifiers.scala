package stainless
package proof

import stainless.lang._
import stainless.annotation._
import stainless.lang.StaticChecks._

import scala.language.postfixOps

@library
object BoundedQuantifiers {

  def intForall(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(n >= 0)
    decreases(n)
    if (n <= 0) true
    else p(n-1) && intForall(n-1,p)
  }

  def intExists(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(n >= 0)
    decreases(n)
    if (n <= 0) false
    else p(n-1) || intExists(n-1,p)
  }

  def intForall2(n: BigInt, m: BigInt, p: (BigInt, BigInt) => Boolean): Boolean = {
    require(n >= 0 && m >= 0)
    decreases(n + m)
    if (n <= 0 || m <= 0) true
    else p(n-1,m-1) && intForall2(n-1, m, p) && intForall2(n, m-1, p)
  }

  @opaque
  def elimForall(n: BigInt, p: BigInt => Boolean, i: BigInt): Unit = {
    require(0 <= i && i < n && intForall(n, p))
    decreases(n)

    if (n > 0 && i < n-1)
      elimForall(n-1, p, i)

  } ensuring(_ => p(i))

  def elimForall2(n: BigInt, m: BigInt, p: (BigInt, BigInt) => Boolean, i: BigInt, j: BigInt): Boolean = {
    require(0 <= i && i < n && 0 <= j && j < m && intForall2(n, m, p))
    decreases(n + m)

    if (i == n-1 && j == m-1) p(i,j)
    else if (i < n-1) elimForall2(n-1, m, p, i, j) && p(i,j)
    else elimForall2(n, m-1, p, i, j) && p(i,j)

  } holds


  def elimExists(n: BigInt, p: BigInt => Boolean): BigInt = {
    require(n >= 0 && intExists(n, p))
    decreases(n)

    if (p(n-1)) n-1
    else elimExists(n-1, p)

  } ensuring(res => p(res))



  def notExistsImpliesForall(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(n >= 0 && !intExists(n,p))
    decreases(n)

    if (n <= 0)
      intForall(n,(i: BigInt) => !p(i))
    else
      notExistsImpliesForall(n-1, p) &&
      intForall(n,(i: BigInt) => !p(i))
  } holds


  def notForallImpliesExists(n: BigInt, p: BigInt => Boolean): Boolean = {
    require(n >= 0 && !intForall(n,p))
    decreases(n)

    if (n <= 0) false
    else if (!p(n-1))
      intExists(n, (i: BigInt) => !p(i))
    else
      notForallImpliesExists(n-1,p) &&
      intExists(n, (i: BigInt) => !p(i))
  } holds

  def witnessImpliesExists(n: BigInt, p: BigInt => Boolean, i: BigInt): Boolean = {
    require(0 <= i && i < n && p(i))
    decreases(n)

    if (i == n-1)
      intExists(n,p)
    else
      witnessImpliesExists(n-1, p, i) &&
      intExists(n, p)
  } holds

  def increment(i: BigInt, n: BigInt): BigInt = {
    require(0 <= i && i < n)
    if (i < n-1) i+1
    else BigInt(0)
  } ensuring(res => 0 <= res && res < n)

  def decrement(i: BigInt, n: BigInt): BigInt = {
    require(0 <= i && i < n)
    if (i == 0) n-1
    else i-1
  } ensuring(res => 0 <= res && res < n)
}
