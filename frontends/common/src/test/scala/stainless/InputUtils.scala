/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import scala.language.existentials

import extraction.xlang.{ trees => xt, TreeSanitizer }
import frontend.CallBack
import utils.CheckFilter

import scala.collection.mutable.ListBuffer

import java.io.{ File, BufferedWriter, FileWriter }

trait InputUtils {

  type Filter = CheckFilter { val trees: xt.type }

  /** Compile and extract the given files' **content** (& the library). */
  def load(contents: Seq[String], filterOpt: Option[Filter] = None)
          (implicit ctx: inox.Context): (Seq[xt.UnitDef], Program { val trees: xt.type }) = {
    val files = contents.map { content =>
      val file = File.createTempFile("stainless", ".scala")
      file.deleteOnExit()
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
      file.getAbsolutePath
    }

    loadFiles(files, filterOpt)
  }

  /** Compile and extract the given files (& the library). */
  def loadFiles(files: Seq[String], filterOpt: Option[Filter] = None)
               (implicit ctx: inox.Context): (Seq[xt.UnitDef], Program { val trees: xt.type }) = {

    // Use the callback to collect the trees.
    val units = ListBuffer[xt.UnitDef]()
    val cls = ListBuffer[xt.ClassDef]()
    val funs = ListBuffer[xt.FunDef]()
    var syms = xt.NoSymbols
    var done = false

    def updateSyms(cls: Seq[xt.ClassDef], funs: Seq[xt.FunDef]) = {
      syms = syms.withClasses(cls).withFunctions(funs)
    }

    val callback = new CallBack {
      override def join(): Unit = ()
      override def stop(): Unit = ()
      override def failed(): Unit = ()
      override def getReport = None

      override def beginExtractions(): Unit = ()

      override def apply(file: String, unit: xt.UnitDef,
                         classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
        units += unit
        cls ++= classes
        funs ++= functions

        updateSyms(classes, functions)
      }

      override def endExtractions(): Unit = {
        done = true
      }
    }

    val compiler = Main.factory(ctx, files, callback)
    compiler.run()

    // Wait for compilation to finish to produce the whole program
    compiler.join()

    // Ensure the callback yields all classes and functions (unless using a custom filter)
    assert(done)

    // Check that extracted symbols are valid
    TreeSanitizer(xt) check syms

    (units.sortBy(_.id.name), inox.Program(xt)(syms))
  }

}

