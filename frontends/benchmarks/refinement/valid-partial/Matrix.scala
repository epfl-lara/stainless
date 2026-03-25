package matrixMut

import stainless.annotation.{ignore, extern}

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
  def ofDim(size: Pos): {res: CheckedArray with res.size == size} =
    CheckedArray(size).asInstanceOf[{res: CheckedArray with res.size == size}]

case class Matrix(width: Dim, height: Dim):
  private val size = width * height
  private val data = CheckedArray.ofDim(size.asInstanceOf[Pos])

  def forRange(from: Pos, to: Dim with to >= from)(body: { i: Pos with from <= i && i < to } => Unit): Unit =
    var i: (Pos with from <= i && i <= to) = from.asInstanceOf[{ i: Pos with from <= i && i <= to }]
    while i < to do
      body(i.asInstanceOf[{i: Pos with from <= i && i < to}])
      i = (i + 1).asInstanceOf[{ i: Pos with from <= i && i <= to }]

  def index(i: Pos with i < height, j: Pos with j < width): {res: Pos with res < data.size} =
    (i * width + j).ck

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
    Matrix(width, height).ck

def Test =
  val m1 = Matrix.ofDim(2, 3)
  val m2 = Matrix.ofDim(3, 2)
//   m1.mul(m2)

//   val m1T = m1.transpose()
//   m1T.mul(m1)

extension [T](x: T)
  @ignore
  inline def ck[TT] = x.asInstanceOf[TT]