import leon.lang._

object Simple {

  def passing_1(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 0))
    f(10)
  } ensuring { res => res > 0 }

  def passing_2(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 1))
    f(1) + f(2)
  } ensuring { res => res > 2 }

  def passing_3(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => f(a) > 0 || f(a) < 0))
    f(8)
  } ensuring { res => res != 0 }

  def passing_4(f: BigInt => BigInt, g: BigInt => BigInt, x: BigInt) = {
    require(forall((a: BigInt, b: BigInt) => f(a) + f(b) > 0))
    if(x <= 0) f(x) + f(x)
    else x
  } ensuring { res => res > 0 }

  def passing_5(f: BigInt => BigInt, g: BigInt => Boolean): BigInt = {
    require(forall((a: BigInt) => if(g(a)) { f(a) > 0 || f(a) < 0 } else { f(a) == 0 }))
    if(g(8)) f(8)
    else BigInt(1)
  } ensuring { res => res != 0 }

  def passing_6(f: BigInt => BigInt, x: BigInt) = {
    require(x > 0 && forall((a: BigInt) => a > 0 ==> f(a) > 0))
    if(x > 0) f(1)
    else f(-1)
  } ensuring { res => res > 0 }

  def passing_7(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 0))
    val a = f(-1)
    f(2)
  } ensuring { res => res > 0 }

}
