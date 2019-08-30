package stainless
package macros

import scala.reflect.macros.blackbox
import scala.language.experimental.macros

object FileProvider {
  def getFileContents(file: String): String = macro impl

  def impl(c: blackbox.Context)(file: c.Tree): c.Tree = {
    import c.universe._
    file match {
      case q"${name: String}" =>
        val content = scala.io.Source.fromFile(name).mkString
        q"$content"
      case  _=>
        c.abort(file.pos, "Not a literal string") }
    }
}
