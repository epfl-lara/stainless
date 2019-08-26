package stainless

import java.io.File
import scala.util.Try
import inox.OptionDef

sealed abstract class OptionOrDefault[+A]
object OptionOrDefault {
  case class  Some[A](get: A) extends OptionOrDefault[A]
  case object None            extends OptionOrDefault[Nothing]
  case object Default         extends OptionOrDefault[Nothing]
}

case class FileOptionDef(name: String) extends OptionDef[OptionOrDefault[File]] {
  val parser = {
    case ""      => Some(OptionOrDefault.None)
    case "false" => Some(OptionOrDefault.None)
    case path    => Try(OptionOrDefault.Some(new File(path))).toOption
  }

  val default  = OptionOrDefault.Default
  val usageRhs = "FILE"
}
