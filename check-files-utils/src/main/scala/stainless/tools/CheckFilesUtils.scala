package stainless.tools

import inox.OptionParsers.OptionParser
import inox.solvers.optCheckModels
import inox.{Context, DebugSection, OptionDef, OptionParsers, OptionValue, Options, OptionsHelpers, optSelectedSolvers, optTimeout, utils}
import stainless.{DefaultReporter, frontend, frontends, termination, verification}
import stainless.frontend.{BatchedCallBack, optBatchedProgram}
import stainless.termination.{optCheckMeasures, optInferMeasures}
import stainless.utils.YesNoOnly
import stainless.verification.{VerificationComponent, VerificationReport, optStrictArithmetic, optVCCache}

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.concurrent.duration.*
import scala.jdk.StreamConverters.*

object CheckFilesUtils {

  case class Args(allFiles: Seq[File], ignoreFiles: Seq[File], parallelism: Option[Int], ctx: Context) {
    def actualFiles: Seq[File] = (allFiles.toSet -- ignoreFiles).toSeq
  }

  object optIgnoreFiles extends OptionDef[Seq[String]] {
    val name = "ignore"
    val default = Seq[String]()
    val parser = OptionParsers.seqParser(OptionParsers.stringParser)
    val usageRhs = "file1,file2,..."
  }
  object optParallelism extends OptionDef[Int] {
    override val name: String = "parallelism"
    override def default: Int = 1
    override def parser: OptionParser[Int] = _.toIntOption.filter(_ > 0)
    override def usageRhs: String = "n"
  }

  val defaultStainlessOptions = Options(Seq(
    optSelectedSolvers(Set("smt-z3")),
    optTimeout(120.seconds),
    optVCCache(true),
    optStrictArithmetic(false),
    optBatchedProgram(true),
    optInferMeasures(false),
    optCheckModels(true),
    optCheckMeasures(YesNoOnly.No),
  ))
  val stainlessValidOptions = Seq(
    optSelectedSolvers,
    optTimeout,
    optVCCache,
    optStrictArithmetic,
    optInferMeasures,
    optCheckModels,
    optCheckMeasures
  )
  val toolOptions = Seq(optIgnoreFiles, optParallelism)
  val allOptions = stainlessValidOptions ++ toolOptions

  val benchmarkPrefix = "../frontends/benchmarks/"
  val help = {
    val toolOpts = toolOptions.map(_.usageDesc).mkString(" ")
    val stainlessOpts = stainlessValidOptions.map(_.usageDesc).mkString(" ")
    s"Usage: check-files-util/run <files or folders> [$toolOpts] [-- $stainlessOpts]"
  }

  def main(argsStr: Array[String]): Unit = {
    if (argsStr.isEmpty) {
      println(help)
    } else {
      val args = parseArgs(argsStr.toSeq)
      val nonExistingIgnoredFiles = args.ignoreFiles.filterNot(_.exists())
      if (nonExistingIgnoredFiles.nonEmpty) {
        warnPrintln(
          "The following --ignore files do not actually exist:" +:
          nonExistingIgnoredFiles.map(f => s"  $f")
        )
      }
      val theFiles = args.actualFiles
      if (theFiles.isEmpty) {
        println("No files were found for the given arguments")
      } else {
        args.parallelism.foreach(p => System.setProperty("parallel", p.toString))
        run(theFiles)(using args.ctx)
      }
    }
  }

  def parseArgs(args: Seq[String]): Args = {
    val (toolAllArgs, stainlessOptions) = args.span(_ != "--")
    val (toolOptsArgs, filesArgs) = toolAllArgs.partition(_.startsWith("--"))
    val files = getFiles(filesArgs)
    val toolParsedOpts = parseOptions(toolOptions, toolOptsArgs)
    val ignoreFiles = toolParsedOpts.findOptionOrDefault(optIgnoreFiles)
      .map(f => File(s"$benchmarkPrefix$f"))
    val parallelism = toolParsedOpts.findOptionOrDefault(optParallelism)
    val parallelismOptional = if (parallelism == 1) None else Some(parallelism)

    val ctx = createContext(stainlessOptions.drop(1))
    Args(files, ignoreFiles, parallelismOptional, ctx)
  }

  def createContext(args: Seq[String]): Context = {
    val parsedStainlessOpts = parseOptions(stainlessValidOptions, args)
    val combinedOpts = defaultStainlessOptions ++ parsedStainlessOpts
    val reporter = SimpleReporter()
    Context(
      reporter = reporter,
      interruptManager = new utils.InterruptManager(reporter),
      options = combinedOpts
    )
  }

  def parseOptions(options: Seq[OptionDef[?]], args: Seq[String]): Options = {
    // Adapted from Inox MainHelpers#parseArguments
    Options(args.map { opt =>
      val (name, value) = OptionsHelpers.nameValue(opt).getOrElse(sys.error(
        s"Malformed option $opt. Options should have the form --name or --name=value"
      ))

      val df = options.find(_.name == name).getOrElse(sys.error(
        s"Unknown option: $name\nValid options are ${options.map(_.name).mkString(", ")}"
      ))
      df.parse(value)(using new DefaultReporter(Set.empty))
    })
  }

  def run(files: Seq[File])(using ctx: Context): Unit = {
    val factory = new frontends.dotc.DottyCompiler.Factory(Nil, Seq.empty)
    val cb = BatchedCallBack(Seq(VerificationComponent))
    val frontend = factory(ctx, files.map(_.getPath), cb)
    frontend.run()
    frontend.join()

    val records = frontend.getReport match {
      case Some(cb.Report(Seq(report: cb.RunReport))) =>
        report.report match {
          case v: VerificationReport => v.results
          case other => sys.error(s"Expected to get a VerificationReport but got $other")
        }
      case other => sys.error(s"Expected to get a Some(cb.Report(Seq(cb.RunReport))) but got $other")
    }
    // We must shut down the executor service, otherwise the process will hang when using parallelism!
    stainless.shutdown()
    writeResults(files, records)
  }

  def writeResults(allFiles: Seq[File], records: Seq[VerificationReport.Record]): Unit = {
    def line(record: VerificationReport.Record): String = {
      val kind =
        // Preconditions are set as VCKind.Info which adds the calling information
        if (record.kind.startsWith("precond.")) "precondition"
        else record.kind
      val status =
        // Status.Inconclusive includes a reason as a string, which we do not want here
        if (record.status.isInconclusive) "inconclusive"
        // "Trivial" VCs depends on the simplifier which we do not want
        // "Valid from cache" depends on the order of VCs solving, and is usually disabled in integration tests
        else if (record.status.isTrivial || record.status.isValidFromCache) "valid"
        else record.status.name
      s"${record.pos.line}:${record.pos.col};${record.id.name};$kind;$status"
    }
    def write(file: File, records: Seq[VerificationReport.Record]): Unit = {
      val path = Paths.get(file.getPath.replace(".scala", ".check"))
      val lines = records.map(line)
      Files.write(path, lines.mkString("\n").getBytes(StandardCharsets.UTF_8))
    }
    val byFile = records.groupBy(_.pos.file).view.mapValues(_.sortBy(_.pos)).toMap
    val withoutFiles = byFile.get(null)
    val withFiles = byFile - null
    withoutFiles.foreach { records =>
      val header = "Some records do not have an associated file:"
      val recsStr = records.map(r => s"  ${line(r)}")
      warnPrintln(header +: recsStr)
      val possibleCandidates = allFiles.toSet -- byFile.keySet
      if (possibleCandidates.nonEmpty) {
        val header = "It could be possible that the set of affected files contains the following files:"
        val prefix = Paths.get(benchmarkPrefix)
        val filesStr = possibleCandidates.toSeq
          .sortBy(_.getPath)
          .map(f => s"  ${prefix.relativize(f.toPath).toFile.getPath}")
        warnPrintln(header +: filesStr)
      }
    }
    withFiles.foreach(write)
  }

  def getFiles(args: Seq[String]): Seq[File] = {
    args.map(f => Paths.get(s"$benchmarkPrefix$f"))
      .flatMap { p =>
        // Note that Path::endsWith has not the behaviour we expect w.r.t. checking extension,
        // we hence convert it first to a plain string.
        if (Files.isRegularFile(p)) {
          if (p.toString.endsWith(".scala")) Seq(p)
          else Seq.empty
        } else {
          Files.walk(p).toScala(Seq)
            .filter(p => Files.isRegularFile(p) && p.toString.endsWith(".scala"))
        }
      }
      .map(_.toFile).distinctBy(_.getPath)
  }

  def warnPrintln(lines: Seq[String]): Unit = {
    lines.foreach { l =>
      val warn = s"${Console.BOLD}${Console.YELLOW}[warning]${Console.RESET}"
      val msg = s"${Console.YELLOW}$l${Console.RESET}"
      println(s"$warn $msg")
    }
  }

  class SimpleReporter extends DefaultReporter(Set.empty) {
    val msgs: mutable.ArrayBuffer[Message] = mutable.ArrayBuffer()

    override def clearProgress(): Unit = ()

    override def doEmit(msg: Message): Unit = msgs += msg

    override def debug(pos: utils.Position, msg: => Any)(using DebugSection): Unit =
      super.debug(pos, msg)

    override def doEmit(msg: ProgressMessage, prevLength: Int): String = {
      println(msg.msg.toString)
      msg.msg.toString
    }
  }
}
