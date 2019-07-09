/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt, TreeSanitizer}

import scala.util.{Try, Success, Failure}
import scala.concurrent.Await
import scala.concurrent.duration._

class BatchedCallBack(components: Seq[Component])(implicit val context: inox.Context) extends CallBack with StainlessReports {
  import context.reporter

  private implicit val debugSection = DebugSectionFrontend

  private var currentClasses = Seq[xt.ClassDef]()
  private var currentFunctions = Seq[xt.FunDef]()
  private var currentTypeDefs = Seq[xt.TypeDef]()

  private var report: AbstractReport[Report] = _

  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline
  private[this] val runs = components.map(_.run(pipeline))

  def beginExtractions(): Unit = {}

  override def apply(
    file: String,
    unit: xt.UnitDef,
    classes: Seq[xt.ClassDef],
    functions: Seq[xt.FunDef],
    typeDefs: Seq[xt.TypeDef]
  ): Unit = {
    reporter.debug(s"Got a unit for $file: ${unit.id} with:")
    reporter.debug(s"\tfunctions -> [${functions.map { _.id }.sorted mkString ", "}]")
    reporter.debug(s"\tclasses   -> [${classes.map { _.id }.sorted mkString ", "}]")
    reporter.debug(s"\ttype defs -> [${typeDefs.map { _.id }.sorted mkString ", "}]")

    this.synchronized {
      currentFunctions ++= functions
      currentClasses ++= classes
      currentTypeDefs ++= typeDefs
    }
  }

  def failed(): Unit = {}

  def endExtractions(): Unit = {
    implicit val popts = xt.PrinterOptions.fromContext(context)

    def rewriteSymbols(symbols: xt.Symbols): xt.Symbols = {
      // remove library flag from all classes and laws that have subclasses without @library
      ???
    }
  
    def keepDefinition(defn: xt.Definition, symbols: xt.Symbols): Boolean = {
      if(defn.flags.contains(xt.Synthetic))
        false
      else defn match {
        case cd: xt.ClassDef => !cd.flags.exists(f => f.name == "library")
        case td: xt.TypeDef => !td.flags.exists(f => f.name == "library")
        case fn: xt.FunDef =>
          val isLibrary = fn.flags.exists(f => f.name == "library")
  
          if (fn.isLaw)
            if(isLibrary) {
              val optClass = fn.getClassDef(symbols)
  
              optClass match {
                case None => false
                case Some(cd) => {
  
                  (for {
                    subclass <- cd.descendants(symbols)
                    
                    if !subclass.flags.exists(f => f.name == "library")
                    if !subclass.methods(symbols).map(symbols.getFunction).exists(subFn => subFn.id.name == fn.id.name && subFn.flags.exists(flag => flag.name == "library"))
                  } yield subclass).nonEmpty
                }
              }
  
            } else
              true
          else
            !isLibrary
      }
    }

    val allSymbols = xt.NoSymbols
      .withClasses(currentClasses)
      .withFunctions(currentFunctions)
      .withTypeDefs(currentTypeDefs)

    def notUserFlag(f: xt.Flag) = f.name == "library" || f == xt.Synthetic

    val userIds =
      currentClasses.filter(cd => keepDefinition(cd, allSymbols)).map(_.id) ++
      currentFunctions.filter(fd => keepDefinition(fd, allSymbols)).map(_.id) ++
      currentTypeDefs.filter(td => keepDefinition(td, allSymbols)).map(_.id)
    
    // println(userIds.map(_.asString))

    val userDependencies = userIds.flatMap(id => allSymbols.dependencies(id)) ++ userIds
    val keepGroups = context.options.findOptionOrDefault(optKeep)

    def hasKeepFlag(flags: Seq[xt.Flag]) =
      keepGroups.exists(g => flags.contains(xt.Annotation("keep", Seq(xt.StringLiteral(g)))))

    val preSymbols =
      xt.NoSymbols.withClasses(currentClasses.filter(cd => hasKeepFlag(cd.flags) || userDependencies.contains(cd.id)))
                  .withFunctions(currentFunctions.filter(fd => hasKeepFlag(fd.flags) || userDependencies.contains(fd.id)))
                  .withTypeDefs(currentTypeDefs.filter(td => hasKeepFlag(td.flags) || userDependencies.contains(td.id)))

    // println(preSymbols.asString)

    val symbols = Recovery.recover(preSymbols)

    try {
      TreeSanitizer(xt).check(symbols)
    } catch {
      case e: extraction.MalformedStainlessCode =>
        reportError(e.tree.getPos, e.getMessage, symbols)
    }

    try {
      symbols.ensureWellFormed
    } catch {
      case e: symbols.TypeErrorException =>
        reportError(e.pos, e.getMessage, symbols)
      case e @ xt.NotWellFormedException(defn, _) =>
        reportError(defn.getPos, e.getMessage, symbols)
    }

    val reports = runs map { run =>
      val ids = symbols.functions.keys.toSeq
      val analysis = Try(run(ids, symbols, filterSymbols = true))
      analysis match {
        case Success(analysis) =>
          val report = Await.result(analysis, Duration.Inf).toReport
          RunReport(run)(report)

        case Failure(err) =>
          val msg = s"Run has failed with error: $err\n\n" +
                    err.getStackTrace.map(_.toString).mkString("\n")

          reporter.fatalError(msg)
      }
    }

    report = Report(reports)
  }

  def stop(): Unit = {
    currentClasses = Seq()
    currentFunctions = Seq()
    currentTypeDefs = Seq()
  }

  def join(): Unit = {}

  def getReport = Option(report)

  private def reportError(pos: inox.utils.Position, msg: String, syms: xt.Symbols): Unit = {
    reporter.error(pos, msg)
    reporter.error(s"The extracted program in not well formed.")
    reporter.error(s"Symbols are:")
    reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.error(s"typedefs  -> [\n  ${syms.typeDefs.values mkString "\n  "}\n]")
    reporter.fatalError(s"Aborting from BatchedCallBack")
  }
}
