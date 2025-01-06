package stainless

import java.io.File
import scala.sys.process.*

object Utils {
  def runCommand(cmd: String): (List[String], Int) = {
    val std = scala.collection.mutable.ListBuffer[String]()
    val exitCode = cmd ! ProcessLogger(std append _)
    (std.toList, exitCode)
  }

  def runMainWithArgs(args: Array[String]): (inox.Context, Option[AbstractReport[?]]) = {
    val ctx = Main.setup(args).copy(reporter = new inox.TestSilentReporter())
    val compilerArgs = args.toList filterNot { _.startsWith("--") }
    val compiler = frontend.build(ctx, compilerArgs, stainless.Main.factory)
    ctx.reporter.info(s"Running: stainless ${args.mkString(" ")}")
    compiler.run()
    compiler.join()
    (ctx, compiler.getReport)
  }

  def getFolders(dir: String): Seq[String] = {
    Option(getClass.getResource(s"/$dir")).toSeq.flatMap { dirUrl =>
      val dirFile = new File(dirUrl.getPath)
      Option(dirFile.listFiles().toSeq).getOrElse(Seq.empty).filter(_.isDirectory)
        .map(_.getName)
    }.sorted
  }
}
