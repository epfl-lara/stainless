/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{ trees => xt }
import frontend.CallBack

import scala.collection.mutable.ListBuffer

import java.io.{ File, BufferedWriter, FileWriter }

trait InputUtils {

  /** Compile and extract the given files' **content** (& the library). */
  def load(context: inox.Context, contents: Seq[String]):
          (Seq[xt.UnitDef], Program { val trees: xt.type }) = {

    val files = contents.map { content =>
      val file = File.createTempFile("stainless", ".scala")
      file.deleteOnExit()
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
      file.getAbsolutePath
    }

    loadFiles(context, files)
  }

  /** Compile and extract the given files (& the library). */
  def loadFiles(context: inox.Context, files: Seq[String]):
               (Seq[xt.UnitDef], Program { val trees: xt.type }) = {

    // Use the callback to collect the trees.
    val units = ListBuffer[xt.UnitDef]()
    val cls = ListBuffer[xt.ClassDef]()
    val funs = ListBuffer[xt.FunDef]()

    val callback = new CallBack {
      override def join(): Unit = ()
      override def stop(): Unit = ()
      override def getReports = Seq.empty

      override def beginExtractions(): Unit = ()
      override def apply(file: String, unit: xt.UnitDef,
                         classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
        units += unit
        cls ++= classes
        funs ++= functions
      }
      override def endExtractions(): Unit = ()
    }

    val compiler = Main.factory(context, files, callback)
    compiler.run()

    // Wait for compilation to finish to produce the whole program
    compiler.join()

    val syms = xt.NoSymbols.withClasses(cls.toSeq).withFunctions(funs.toSeq)

    val program = new inox.Program {
      val trees: xt.type = xt
      val ctx = context
      val symbols = syms
    }

    (units.toSeq, program)
  }

}

