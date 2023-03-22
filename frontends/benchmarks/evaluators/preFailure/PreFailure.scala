import stainless.collection._

object PreFailure {
  sealed trait Topping
  case object Mozzarella extends Topping
  case object Pineapple extends Topping
  case object Capers extends Topping

  case class Pizza(size: BigInt, toppings: List[Topping])

  def addTopping(p: Pizza, t: Topping): Pizza = {
    require(t != Pineapple)
    p.copy(toppings = t :: p.toppings)
  }

  val base = Pizza(42, List(Mozzarella))
  def ohno: Pizza =
    addTopping(addTopping(base, Capers), Pineapple)
}