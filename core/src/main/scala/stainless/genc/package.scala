package stainless

import extraction.throwing.trees._

package object genc {
  object DebugSectionGenC extends inox.DebugSection("genc")

  object optOutputFile extends inox.OptionDef[String] {
    val name = "genc-output"
    val default = "stainless.c"
    val usageRhs = "file"
    val parser = inox.OptionParsers.stringParser
  }

  // FIXME: see leon definition
  def pathFromRoot(df: Definition)(implicit syms: Symbols): List[Definition] = List(df)
}
