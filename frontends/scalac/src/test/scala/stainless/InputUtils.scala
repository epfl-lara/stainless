/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}
import java.io.{File, BufferedWriter, FileWriter}

trait InputUtils {

  def load(ctx: inox.Context, contents: Seq[String], compilerOpts: Seq[String] = Seq.empty):
          (Seq[xt.UnitDef], Program { val trees: xt.type }) = {

    val files = contents.map { content =>
      val file = File.createTempFile("stainless", ".scala")
      file.deleteOnExit()
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
      file.getAbsolutePath
    }

    val allOpts = Main.libraryFiles ++ files ++ compilerOpts
    Main.extractFromSource(ctx, allOpts.toList)
  }
}
