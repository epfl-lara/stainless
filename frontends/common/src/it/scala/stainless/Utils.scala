package stainless

import sys.process._

object Utils {
  def runCommand(cmd: String): (List[String], Int) = {
    val std = scala.collection.mutable.ListBuffer[String]()
    val exitCode = cmd ! ProcessLogger(std append _)
    (std.toList, exitCode)
  }

  def runMainWithArgs(args: Array[String]) = {
    val ctx = Main.setup(args).copy(reporter = new inox.TestSilentReporter())
    val compilerArgs = args.toList filterNot { _.startsWith("--") }
    var compiler = frontend.build(ctx, compilerArgs, stainless.Main.factory)
    ctx.reporter.info(s"Running: stainless ${args.mkString(" ")}")
    compiler.run()
    compiler.join()
    (ctx, compiler.getReport)
  }
}
