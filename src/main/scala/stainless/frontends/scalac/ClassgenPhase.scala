/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package frontends.scalac

import utils._

import scala.tools.nsc.{Settings,CompilerCommand}
import java.io.File
import java.nio.file.Files

object ClassgenPhase extends LeonPhase[List[String], List[String]] {

  val optExtern = LeonFlagOptionDef("extern", "Run @extern function on the JVM", false)

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optExtern)

  val name = "Scalac .class generation"
  val description = "Generation of .class for evaluation of @extern functions"

  implicit val debug = DebugSectionTrees

  def run(ctx: LeonContext, args: List[String]): (LeonContext, List[String]) = {
    if (ctx.findOptionOrDefault(optExtern)) {
      val timer = ctx.timers.frontend.extern.start()

      val settings = new Settings

      val scalaLib = Option(scala.Predef.getClass.getProtectionDomain.getCodeSource).map{
        _.getLocation.getPath
      }.orElse( for {
        // We are in Eclipse. Look in Eclipse plugins to find scala lib
        eclipseHome <- Option(System.getenv("ECLIPSE_HOME"))
        pluginsHome = eclipseHome + "/plugins"
        plugins <- scala.util.Try(new File(pluginsHome).listFiles().map{ _.getAbsolutePath }).toOption
        path <- plugins.find{ _ contains "scala-library"}
      } yield path).getOrElse( ctx.reporter.fatalError(
        "No Scala library found. If you are working in Eclipse, " +
        "make sure to set the ECLIPSE_HOME environment variable to your Eclipse installation home directory"
      ))

      val tempOut = Files.createTempDirectory("classes").toFile

      settings.classpath.value   = scalaLib
      settings.usejavacp.value   = false
      settings.deprecation.value = true
      settings.outdir.value      = tempOut.getPath

      val compilerOpts = Build.libFiles ::: args.filterNot(_.startsWith("--"))

      val command = new CompilerCommand(compilerOpts, settings) {
        override val cmdName = "leon"
      }

      if(command.ok) {
        // Debugging code for classpath crap
        // new scala.tools.util.PathResolver(settings).Calculated.basis.foreach { cp =>
        //   cp.foreach( p =>
        //     println(" => "+p.toString)
        //   )
        // }


        val compiler = new FullScalaCompiler(settings, ctx)
        val run = new compiler.Run
        run.compile(command.files)

        timer.stop()

        val ctx2 = ctx.copy(classDir = Some(tempOut))

        (ctx2, args)
      } else {
        ctx.reporter.fatalError("No input program.")
      }
    } else {
      (ctx, args)
    }
  }
}

