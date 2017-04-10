package termination
package usermeasure.higherorder

import stainless._
import lang._
import annotation._
import collection._

object CFATest {

  /*def test1(f: (Unit => BigInt) => BigInt, xs: BigInt): BigInt = {
    val l = (u: Unit) => xs
    f(l)
  }

  def test2(): BigInt = {
    val f = (l: Unit => BigInt) => l(())
    test1(f, BigInt(0))
  }

  def test3(g: Unit => (Unit => BigInt) => BigInt): BigInt = {
    test1(g(()), BigInt(0))
  }

  def test4(g: (BigInt => BigInt) => BigInt, x: BigInt): BigInt = {
    val l = (y: BigInt) => test4(g, y)
    g(l)
  }

  def baddy() = {
    test4((l: (BigInt => BigInt)) => l(0), 0)
  }*/

  case class SCons(x: BigInt, tailFun: () => SCons)

  def test5(f: (Unit => SCons) => SCons, xs: SCons): SCons = {
    xs match {
      case SCons(x, tfun) =>
        f(Unit => test5(f, tfun()))
    }
  }
  
  /*  def zipWithFun(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    (xs, ys) match {
      case (SCons(x, _), SCons(y, _)) =>
        SCons(f(x, y), () => zipWithFun(f, xs.tailFun(), ys.tailFun()))
    }
  }*/

}