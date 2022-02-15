package stainless

import inox.OptionParsers.{OptionParser, stringParser}

import java.io.File

package object testgen {

  object optOutputFile extends FileOptionDef {
    val name = "testgen-file"
    val default = new File("TestCases.scala")
  }

  object optGenCIncludes extends inox.SeqOptionDef[String] {
    override val elementParser: OptionParser[String] = stringParser

    override val name: String = "genc-testgen-includes"

    override def default: Seq[String] = Seq("stainless.h")

    override def usageRhs: String = "header1.h,header2.h,..."
  }

}
