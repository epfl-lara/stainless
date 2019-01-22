object NumericTests {
  def associativity(x: Float, y: Float, z: Float): Boolean = {
    (x + y) + z == x + (y + z)
  }.holds
}
