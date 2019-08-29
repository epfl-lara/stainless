/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

object SlowTests {
  private lazy val _enabled: Boolean = {
    sys.env
      .get("RUN_SLOW_TESTS")
      .map {
        case "true" => true
        case _      => false
      }
      .getOrElse(false)
  }

  def enabled: Boolean = _enabled
  def disabled: Boolean = !_enabled
}
