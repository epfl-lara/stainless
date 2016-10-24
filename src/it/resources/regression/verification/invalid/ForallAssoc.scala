/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object ForallAssoc {

  /*
  def test3(f: (BigInt, BigInt) => BigInt): Boolean = {
    require(forall((x: BigInt, y: BigInt, z: BigInt) => f(x, f(y, z)) == f(f(x, y), z)))
    f(1, f(2, f(3, f(4, 5)))) == f(f(f(f(1, 2), 3), 4), 4)
  }.holds
  */

  def test4(f: (BigInt, BigInt) => BigInt): Boolean = {
    require(forall((x: BigInt, y: BigInt, z: BigInt) => f(x, f(y, z)) == f(f(x, y), z)))
    f(1, f(2, f(3, 4))) == 0
  }.holds

}
