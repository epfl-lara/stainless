import stainless.lang._

object UsingGiven {
  case class PostalAddress(city: String, zipCode: Int, street: String, extra: String)
  // We also profit to test enum classes
  enum Stamp {
    case AMail, BMail
  }

  case class Envelope(msg: String, postalAddress: PostalAddress, stamp: Stamp)

  // To test anonymous given
  given PostalAddress = PostalAddress("Lausanne", 1015, "EPFL IC IINFCOM LARA", "INR 318 (Bâtiment INR), Station 14")
  // To test named given
  given stamp: Stamp = Stamp.AMail // For faster delivery :)

  def mkEnvelope(msg: String)(using pa: PostalAddress, stamp: Stamp): Envelope =
    Envelope(msg, pa, stamp).ensuring(res => res.msg == msg && res.postalAddress == pa && res.stamp == stamp)

  def test1: Boolean = {
    val env1 = mkEnvelope("Greetings LARA!")
    env1.postalAddress == summon[PostalAddress] &&
      env1.stamp == stamp
  }.holds

  def test2: Boolean = {
    val lampAddress = PostalAddress("Lausanne", 1015, "EPFL IC IINFCOM LAMP1", "INR 319 (Bâtiment INR), Station 14")
    val env2 = mkEnvelope("Greetings LAMP!")(using lampAddress)
    env2.postalAddress == lampAddress &&
      env2.stamp == stamp
  }.holds
}