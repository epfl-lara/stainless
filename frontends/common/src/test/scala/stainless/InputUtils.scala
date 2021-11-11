/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import extraction.xlang.{ trees => xt, TreeSanitizer }
import extraction.utils.DebugSymbols
import frontend.{ CallBack, Recovery, RecoveryResult }
import utils.CheckFilter

import scala.collection.mutable.ListBuffer

import java.io.{ File, BufferedWriter, FileWriter }

trait InputUtils {

  type Filter = CheckFilter { val trees: xt.type }

  def compilerVersion: String = Main.compilerVersion

  def isScala2 = compilerVersion.startsWith("2.")

  def isScala3 = compilerVersion.startsWith("3.")

  /** Compile and extract the given files' **content** (& the library). */
  def load(contents: Seq[String], filterOpt: Option[Filter] = None, sanitize: Boolean = true)
          (using inox.Context): (Seq[xt.UnitDef], Program { val trees: xt.type }) = {
    val files = contents.map { content =>
      val file = File.createTempFile("stainless", ".scala")
      file.deleteOnExit()
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
      file.getAbsolutePath
    }

    loadFiles(files, filterOpt, sanitize)
  }

  /** Compile and extract the given files (& the library). */
  def loadFiles(files: Seq[String], filterOpt: Option[Filter] = None, sanitize: Boolean = true)
               (using ctx: inox.Context): (Seq[xt.UnitDef], Program { val trees: xt.type }) = {

    val preprocessing = new DebugSymbols {
      val name = "Preprocessing"
      val context = ctx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    // Use the callback to collect the trees.
    val units = ListBuffer[xt.UnitDef]()
    val cls = ListBuffer[xt.ClassDef]()
    val funs = ListBuffer[xt.FunDef]()
    val tpds = ListBuffer[xt.TypeDef]()
    var syms = xt.NoSymbols
    var done = false

    def updateSyms(cls: Seq[xt.ClassDef], funs: Seq[xt.FunDef], tpds: Seq[xt.TypeDef]) = {
      syms = syms.withClasses(cls).withFunctions(funs).withTypeDefs(tpds)
    }

    val callback = new CallBack {
      override def join(): Unit = ()
      override def stop(): Unit = ()
      override def failed(): Unit = ()
      override def getReport = None

      override def beginExtractions(): Unit = ()

      override def apply(
        file: String,
        unit: xt.UnitDef,
        classes: Seq[xt.ClassDef],
        functions: Seq[xt.FunDef],
        typeDefs: Seq[xt.TypeDef]
      ): Unit = {
        units += unit
        cls ++= classes
        funs ++= functions
        tpds ++= typeDefs

        updateSyms(classes, functions, typeDefs)
      }

      override def endExtractions(): Unit = {
        done = true
        syms = preprocessing.debug(frontend.Preprocessing().transform)(syms)
      }
    }

    val compiler = Main.factory(ctx, files, callback)
    compiler.run()

    // Wait for compilation to finish to produce the whole program
    compiler.join()

    // Ensure the callback yields all classes and functions (unless using a custom filter)
    assert(done)

    if (sanitize) {
      // Check that extracted symbols are valid
      TreeSanitizer(xt) enforce syms
    }

    // Check that extracted symbols are well-formed
    try {
      syms.ensureWellFormed
    } catch {
      case e @ xt.NotWellFormedException(defn, _) =>
        throw new extraction.MalformedStainlessCode(defn, e.getMessage)
    }

    (units.sortBy(_.id.name).toSeq, inox.Program(xt)(syms))
  }

}

