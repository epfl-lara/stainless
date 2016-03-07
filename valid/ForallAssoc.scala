/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object ForallAssoc {

  def ex[A](x1: A, x2: A, x3: A, x4: A, x5: A, f: (A, A) => A) = {
    require(forall {
      (x: A, y: A, z: A) => f(x, f(y, z)) == f(f(x, y), z)
    })

    f(x1, f(x2, f(x3, f(x4, x5)))) == f(f(x1, f(x2, f(x3, x4))), x5)
  }.holds

  def test1(f: (BigInt, BigInt) => BigInt): Boolean = {
    require(forall((x: BigInt, y: BigInt, z: BigInt) => f(x, f(y, z)) == f(f(x, y), z)))
    f(1, f(2, f(3, 4))) == f(f(f(1, 2), 3), 4)
  }.holds

  def test2(f: (BigInt, BigInt) => BigInt): Boolean = {
    require(forall((x: BigInt, y: BigInt, z: BigInt) => f(x, f(y, z)) == f(f(x, y), z)))
    f(1, f(2, f(3, f(4, 5)))) == f(f(f(f(1, 2), 3), 4), 5)
  }.holds

}
