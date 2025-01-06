object SATPrecond3 {
  case class Egg(x: BigInt) 
  case class Chicken(e: Egg)
  def f(x: BigInt, egg: Egg, chicken: Chicken): BigInt = {
    require(x > 0)
    require(egg.x == x)
    require(chicken.e == egg)
    require(chicken.e.x == -1)
    egg.x * 3
  }
}
