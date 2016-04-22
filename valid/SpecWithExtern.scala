import leon.annotation._

object SpecWithExtern {


  //random between returns any value between l and h.
  //For execution via scalac, we pick one valid implementation, but
  //we would like the program to be verified versus any possible
  //implementation, which should happen thanks to @extern
  @extern
  def randomBetween(l: Int, h: Int): Int = {
    require(l <= h)
    l
  } ensuring(res => (res >= l && res <= h))

  //postcondition is wrong, but if leon considers 
  //actual body of randomBetween it would be correct
  def wrongProp(): Int = {
    randomBetween(0, 10)
  } ensuring(res => res >= 0 && res < 10)

}
