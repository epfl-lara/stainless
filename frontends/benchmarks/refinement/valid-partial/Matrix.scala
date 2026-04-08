package matrixMut
import stainless.annotation.{ignore, extern}
import language.experimental.qualifiedTypes.silent

type Dim = {v: Int with v >= 0 && v > 0 && v <= 1000}
type Pos = {v: Int with v >= 0}

final class CheckedArray(val size: Pos):
  @ignore
  private val data = new Array[Double](size)
  @extern
  def apply(i: Pos with i < size): Double = data(i)
  @extern
  def update(i: Pos with i < size, x: Double): Unit = data(i) = x

object CheckedArray:
  def ofDim(size: Pos): {res: CheckedArray with res.size == size} = CheckedArray(size)

case class Matrix(width: Dim, height: Dim):
  private val size: Pos = width * height
  private val data = CheckedArray.ofDim(size)

  def forRange(from: Pos, to: Dim with to >= from)(body: { i: Pos with from <= i && i < to } => Unit): Unit =
    var i: (Pos with from <= i && i <= to) = from
    while i < to do
      body(i)
      i = (i + 1)

  //I don't know how to prove this
  @extern
  def index(i: Pos with i < height, j: Pos with j < width): {res: Pos with res < data.size} =
    (i * width + j).runtimeChecked

  def apply(i: Pos with i < height, j: Pos with j < width): Double =
    data(index(i, j))

  def update(i: Pos with i < height, j: Pos with j < width, x: Double): Unit =
    data(index(i, j)) = x

  def transpose(): {v: Matrix with v.width == height && v.height == width} =
    val transposed = Matrix.ofDim(width = height, height = width)
    forRange(0, height): i =>
      forRange(0, width): j =>
        transposed(j, i) = this(i, j)
    transposed

  def mul(that: Matrix with that.height == width):
    {v: Matrix with v.width == that.width && v.height == height}
  =
    val result = Matrix.ofDim(width = that.width, height = height)
    forRange(0, height): i =>
      forRange(0, that.width): j =>
        var sum = 0.0
        @extern
        def addSum(d: Double): Unit = sum = sum + d
        forRange(0, width): k =>
          addSum(this(i, k) * that(k, j))
        result(i, j) = sum
    result

object Matrix:
  def ofDim(width: Dim, height: Dim): {m: Matrix with m.width == width && m.height == height} =
    Matrix(width, height)

def Test =
  val m1  = Matrix.ofDim(2, 3)
  val m2  = Matrix.ofDim(3, 2)
  val _   = m1.mul(m2)
  val m1T = m1.transpose()
  val _   = m1T.mul(m1)