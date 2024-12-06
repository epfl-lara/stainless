/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import extraction.xlang.{TreeSanitizer, trees as xt}
import extraction.utils.DebugSymbols
import frontend.{CallBack, Recovery, RecoveryResult}
import inox.TestSilentReporter
import utils.CheckFilter

import scala.collection.mutable.ListBuffer
import java.io.{BufferedWriter, File, FileWriter}

trait InputUtils {

  type Filter = CheckFilter { val trees: xt.type }

  case class ExtractionError(errs: Seq[String]) extends Exception(s"Got the following errors:\n${errs.mkString("  ", "\n  ", "")}")
  case class SanitizationError(errs: Seq[String]) extends Exception(s"Got the following errors:\n${errs.mkString("  ", "\n  ", "")}")

  def compilerVersion: String = Main.compilerVersion

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

  /** Compile and extract the given files. */
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
        syms = preprocessing.debugWithoutSummary(frontend.Preprocessing().transform)(syms)._1
      }
    }

    val compiler = Main.factory(ctx, files, callback)
    compiler.run()

    // Wait for compilation to finish to produce the whole program
    compiler.join()

    // Ensure the callback yields all classes and functions (unless using a custom filter)
    assert(done)

    if (ctx.reporter.errorCount != 0) {
      throw ExtractionError(ctx.reporter.errorsOrNil)
    }

    if (sanitize) {
      // Check that extracted symbols are valid
      TreeSanitizer(xt).enforce(syms)
      if (ctx.reporter.errorCount != 0) {
        throw SanitizationError(ctx.reporter.errorsOrNil)
      }
    }

    // Check that extracted symbols are well-formed
    try {
      syms.ensureWellFormed
    } catch {
      case e @ xt.NotWellFormedException(defn, _) =>
        throw extraction.MalformedStainlessCode(defn, e.getMessage)
    }

    (units.sortBy(_.id.name).toSeq, inox.Program(xt)(syms))
  }

  extension (rep: inox.Reporter) {
    def errorsOrNil: Seq[String] = rep match {
      case reporter: TestSilentReporter => reporter.lastErrors
      case _ => Seq.empty
    }
  }
}

