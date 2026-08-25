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

  // How GenC compiles BigInt (IntegerType). Empty (the default) means BigInt is rejected.
  // The same option must be passed to verification, where it injects VCs checking that
  // every BigInt operation's mathematical result fits in the chosen representation.
  object optBigIntAs extends inox.OptionDef[String] {
    val name = "genc-bigint-as"
    val default = ""
    val usageRhs = "uint32"
    val parser = inox.OptionParsers.stringParser
  }

  object optIncludes extends inox.OptionDef[Seq[String]] {
    val name = "genc-includes"
    val default = Seq()
    val usageRhs = "file1.h,file2.h,..."
    val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  }

  def bigIntToUInt32(ctx: inox.Context): Boolean =
    ctx.options.findOptionOrDefault(optBigIntAs) match {
      case "" => false
      case "uint32" => true
      case other =>
        ctx.reporter.fatalError(s"Unsupported --genc-bigint-as value: $other (supported: uint32)")
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
}
