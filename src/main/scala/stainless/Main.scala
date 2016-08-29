/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import dotty.tools.dotc._
import dotty.tools.dotc.core.Contexts._

object Main {
  def main(args: Array[String]): Unit = {
    val inoxCtx = inox.InoxContext.empty

    val driver = new Driver {
      def newCompiler(implicit ctx: Context) = new frontends.dotty.DottyCompiler(inoxCtx)
    }

    val compilerArgs = args.filterNot(_.startsWith("--")) ++ Build.libraryFiles
    driver.process(compilerArgs)
  }
}
