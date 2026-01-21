import stainless.math._
import stainless.annotation.{wrapping => wrappingAnnot}

object FloatingPointWrapping {

  def disablesNaNChecks(f: Float, d: Double): Unit = wrapping {
    f == Float.NaN && f != Float.NaN && f < Float.NaN && f <= Float.NaN && f > Float.NaN && f >= Float.NaN
      && d == Double.NaN && d != Double.NaN && d < Double.NaN && d <= Double.NaN && d > Double.NaN && d >= Double.NaN
  }

  @wrappingAnnot
  def disablesNaNChecks2(f: Float, d: Double): Unit = {
    f == Float.NaN && f != Float.NaN && f < Float.NaN && f <= Float.NaN && f > Float.NaN && f >= Float.NaN
      && d == Double.NaN && d != Double.NaN && d < Double.NaN && d <= Double.NaN && d > Double.NaN && d >= Double.NaN
  }

  def disablesCastCheck(d: Double): Unit = wrapping {
    val b = d.toByte
    val s = d.toShort
    val i = d.toInt
    val l = d.toLong
  }

  @wrappingAnnot
  def disablesCastCheck2(d: Double): Unit = {
    val b = d.toByte
    val s = d.toShort
    val i = d.toInt
    val l = d.toLong
  }

}
