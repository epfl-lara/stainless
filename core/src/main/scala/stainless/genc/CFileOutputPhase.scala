/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter

object CFileOutputPhase extends UnitPhase[CAST.Prog] {

  val name = "C File Output"
  val description = "Output converted C program to the specified file (default leon.c)"

  def apply(ctx: inox.Context, program: CAST.Prog) {
    val timer = ctx.timers.genc.print.start()

    // Get the output file name from command line options, or use default
    val cFileName = ctx.options.findOptionOrDefault(optOutputFile)
    val cOutputFile = new File(cFileName)
    val hFileName = cFileName.stripSuffix(".c") + ".h"
    val hOutputFile = new File(hFileName)

    val parent = cOutputFile.getParentFile()
    try {
      if (parent != null) {
        parent.mkdirs()
      }
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not create directory " + parent)
    }

    // Output C code to the file
    try {
      val cout = new BufferedWriter(new FileWriter(cOutputFile))
      val hout = new BufferedWriter(new FileWriter(hOutputFile))

      val headerDependencies = CASTDependencies.headerDependencies(program)(ctx)

      val ph = new CPrinter(hFileName, false, headerDependencies)
      ph.print(program)
      hout.write(ph.sb.toString)
      hout.close()

      val pc = new CPrinter(hFileName, true, headerDependencies)
      pc.print(program)
      cout.write(pc.sb.toString)
      cout.close()

      ctx.reporter.info(s"Output written to $hOutputFile and $cOutputFile")
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not write C ouptut on " + cOutputFile)
    }

    timer.stop()
  }

}
