package stainless

import extraction.throwing.trees._

package object genc {
  object DebugSectionGenC extends inox.DebugSection("genc")

  // FIXME: see leon definition
  def pathFromRoot(df: Definition)(implicit syms: Symbols): List[Definition] = List(df)
}
