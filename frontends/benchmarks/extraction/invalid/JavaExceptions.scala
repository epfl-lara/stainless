// Java exceptions without a Stainless version cannot be thrown or caught, nor their subclasses.
object JavaExceptions {
  class Mine extends java.io.IOException("mine")

  def io(x: BigInt): BigInt = {
    if (x == 0) throw new java.io.IOException("io")
    x
  }

  def error(x: BigInt): BigInt = {
    if (x == 0) throw new Error("error")
    x
  }

  def mine(x: BigInt): BigInt = {
    if (x == 0) throw new Mine
    x
  }

  def catchIO(x: BigInt): BigInt = try x catch { case _: java.io.IOException => BigInt(0) }
}
