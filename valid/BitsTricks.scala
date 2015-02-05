import leon.annotation._
import leon.lang._

object BitsTricks {

  def bitAt(x: Int, n: Int): Boolean = {
    require(n >= 0 && n < 32)
    ((x >> n) & 1) == 1
  }

  def isEven(x: Int): Boolean = {
    (x & 1) == 0
  } ensuring(res => res == (x % 2 == 0))

  def isNegative(x: Int): Boolean = {
    (x >>> 31) == 1
  } ensuring(b => b == x < 0)

  def isBitNSet(x: Int, n: Int): Int = {
    require(n >= 0 && n < 32)
    (x & (1 << n))
  }

  def testBitSet1(): Int = {
    isBitNSet(122, 3)
  } ensuring(_ != 0)
  def testBitSet2(): Int = {
    isBitNSet(-33, 5)
  } ensuring(_ == 0)

  def setBitN(x: Int, n: Int): Int = {
    require(n >= 0 && n < 32)
    x | (1 << n)
  } ensuring(res => isBitNSet(res, n) != 0)

  def toggleBitN(x: Int, n: Int): Int = {
    require(n >= 0 && n < 32)
    x ^ (1 << n)
  } ensuring(res => 
      if(isBitNSet(x, n) != 0) isBitNSet(res, n) == 0
      else isBitNSet(res, n) != 0)


  def checkDoubleXor(x: Int, y: Int): Int = {
    x ^ y ^ x
  } ensuring(res => res == y)


  def turnOffRightmostOneRec(x: Int, index: Int): Int = {
    require(index >= 0 && index < 32)
    if(bitAt(x, index)) toggleBitN(x, index)//(x ^ (1 << index))
    else if(index == 31) x
    else turnOffRightmostOneRec(x, index + 1)
  }

  /*
   * loops forever on the proof
   */
  def turnOffRightmostOne(x: Int): Int = {
    x & (x - 1)
  } //ensuring(_ == turnOffRightmostOneRec(x, 0))

  // 010100 -> 010111
  def rightPropagateRightmostOne(x: Int): Int = {
    x | (x - 1)
  }

  def property1(x: Int): Boolean = {
    val y = rightPropagateRightmostOne(x)
    y == rightPropagateRightmostOne(y)
  } ensuring(b => b)

  def isRotationLeft(x: Int, y: Int, n: Int, i: Int): Boolean = {
    require(i >= 0 && i <= 32 && n >= 0 && n < 32)
    if(i == 32) 
      true 
    else bitAt(x, i) == bitAt(y, (i + n) % 32) && isRotationLeft(x, y, n, i+1)
  }

  //rotateLeft proves in 1 minute (on very powerful computer)
  def rotateLeft(x: Int, n: Int): Int = {
    require(n >= 0 && n < 32)
    val front = x >>> (32 - n)
    (x << n) | front
  } //ensuring(res => isRotationLeft(x, res, n, 0))

  //careful with overflows, case definition, truncated
  def safeMean(x: Int, y: Int): Int = {
    if(x >= 0 && y <= 0 || x <= 0 && y >= 0) (x + y)/2
    else if(x >= 0 && x <= y) x + (y - x)/2
    else if(x >= 0 && y <= x) y + (x - y)/2
    else if(x <= 0 && x <= y) y + (x - y)/2
    else x + (y - x)/2
  }

  //proves in 45 seconds
  def magicMean(x: Int, y: Int): Int = {
    val t = (x&y)+((x^y) >> 1)
    t + ((t >>> 31) & (x ^ y))
  } //ensuring(res => res == safeMean(x, y))


}
