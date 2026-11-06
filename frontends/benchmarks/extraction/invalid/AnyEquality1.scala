object AnyEquality1:
  def byteInt(): Boolean =
    val a: Any = (5: Byte)
    val b: Any = 5
    a == b

  def number(a: Any): Boolean = a == 5

  def bigInt(a: Any): Boolean = a == BigInt(5)
