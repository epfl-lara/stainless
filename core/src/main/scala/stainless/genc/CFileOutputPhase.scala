/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter

trait CFileOutputPhase extends UnitPhase[CAST.Prog] {

  val name = "C File Output"
  val description = "Output converted C program to the specified file (default leon.c)"

  def apply(program: CAST.Prog) {
    val timer = context.timers.genc.print.start()

    // Get the output file name from command line options, or use default
    val cFileName = context.options.findOptionOrDefault(optOutputFile)
    val cOutputFile = new File(cFileName)
    val hFileName = cFileName.stripSuffix(".c") + ".h"
    val hOutputFile = new File(hFileName)

    val parent = cOutputFile.getParentFile()
    try {
      if (parent != null) {
        parent.mkdirs()
      }
    } catch {
      case _ : java.io.IOException => context.reporter.fatalError("Could not create directory " + parent)
    }

    // Output C code to the file
    try {
      val cout = new BufferedWriter(new FileWriter(cOutputFile))
      val hout = new BufferedWriter(new FileWriter(hOutputFile))

      val headerDependencies = CASTDependencies.headerDependencies(program)(context)

      val ph = new CPrinter(hFileName, false, headerDependencies)
      ph.print(program)
      hout.write(ph.sb.toString)
      hout.close()

      val pc = new CPrinter(hFileName, true, headerDependencies)
      pc.print(program)
      cout.write(pc.sb.toString)
      cout.close()

      context.reporter.info(s"Output written to $hOutputFile and $cOutputFile")
    } catch {
      case _ : java.io.IOException => context.reporter.fatalError("Could not write C ouptut on " + cOutputFile)
    }

    timer.stop()
  }

}

object CFileOutputPhase {
  def apply(implicit ctx: inox.Context): LeonPipeline[CAST.Prog, CAST.Prog] = new {
    val context = ctx
  } with CFileOutputPhase
}
