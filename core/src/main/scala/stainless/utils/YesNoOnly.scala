package stainless
package utils

sealed abstract class YesNoOnly {
  import YesNoOnly._

  def isYes: Boolean  = this == Yes
  def isNo: Boolean   = this == No
  def isOnly: Boolean = this == Only

  def isFalse: Boolean = isNo
  def isTrue: Boolean  = !isNo
}

object YesNoOnly {
  case object Yes  extends YesNoOnly
  case object No   extends YesNoOnly
  case object Only extends YesNoOnly

  def parse(str: String): Option[YesNoOnly] = str match {
    case "yes" | "true" | "on"  => Some(Yes)
    case "no" | "false" | "off" => Some(No)
    case "only"                 => Some(Only)
    case _                      => None
  }
}
