package stainless

import java.io.File
import scala.util.Try
import inox.OptionDef

abstract class FileOptionDef extends OptionDef[File] {
  val parser = {
    case ""      => None
    case "false" => None
    case path    => Try(new File(path)).toOption
  }

  val usageRhs = "FILE"
}
