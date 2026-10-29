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

  object optIncludes extends inox.OptionDef[Seq[String]] {
    val name = "genc-includes"
    val default = Seq()
    val usageRhs = "file1.h,file2.h,..."
    val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  }

  // FIXME: see leon definition
  def pathFromRoot(df: Definition)(using Symbols): List[Definition] = List(df)

  // declaration mode for *global variables*
  sealed abstract class DeclarationMode
  case object Define extends DeclarationMode // #define
  case object Static extends DeclarationMode // static annotation (only for variables, not functions!)
  case object Volatile extends DeclarationMode // volatile annotation
  case object External extends DeclarationMode // no declaration in the produced code
  case object Export extends DeclarationMode // print in header file
  case object Const extends DeclarationMode // const qualifier, for immutable values

  /** Whether a global declaration with the given `modes` is defined in the header file.
    *
    * Exported constants are defined directly in the header file (as `static const`) so that C code can
    * use them; other exported globals are defined in the C file and declared `extern` in the header.
    */
  def isHeaderConstant(modes: Seq[DeclarationMode]): Boolean =
    modes.contains(Export) && modes.contains(Const) && !modes.contains(Define)
}
