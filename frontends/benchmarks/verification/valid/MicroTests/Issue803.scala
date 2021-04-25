

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.lang.StaticChecks._
import scala.annotation._

object verified {

  @tailrec
  def countDown(n: Int): Int = {
    if (n > 0) countDown(n-1)
    else n
  }

  @induct
  def countDownNonneg(n: Int): Unit = {
    require(n >= 0)
    ()
  }.ensuring(_ => countDown(n) <= 0)
}
