/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package frontends.scalac

import purescala.Definitions.Program
import utils._

import scala.tools.nsc.{Settings,CompilerCommand}
import java.io.File

object ExtractionPhase extends SimpleLeonPhase[List[String], Program] {

  val name = "Scalac Extraction"
  val description = "Extraction of trees from the Scala Compiler"

  val optStrictCompilation = LeonFlagOptionDef("strictCompilation", "Exit Leon after an error in compilation", true)

  override val definedOptions: Set[LeonOptionDef[Any]] = Set(optStrictCompilation)

  implicit val debug = DebugSectionTrees

  def apply(ctx: LeonContext, args: List[String]): Program = {
    val timer = ctx.timers.frontend.start()

    val settings = new Settings

    def getFiles(path: String): Option[Array[String]] = 
      scala.util.Try(new File(path).listFiles().map{ _.getAbsolutePath }).toOption
    
    val scalaLib = Option(scala.Predef.getClass.getProtectionDomain.getCodeSource).map{
      _.getLocation.getPath
    }.orElse( for {
      // We are in Eclipse. Look in Eclipse plugins to find scala lib
      eclipseHome <- Option(System.getenv("ECLIPSE_HOME")) 
      pluginsHome = eclipseHome + "/plugins"
      plugins <- getFiles(pluginsHome)
      path <- plugins.find{ _ contains "scala-library"}
    } yield path).getOrElse( ctx.reporter.fatalError(
      "No Scala library found. If you are working in Eclipse, " +
      "make sure to set the ECLIPSE_HOME environment variable to your Eclipse installation home directory"
    ))
    
    settings.classpath.value   = scalaLib
    settings.usejavacp.value   = false
    settings.deprecation.value = true
    settings.Yrangepos.value   = true
    settings.skip.value        = List("patmat")

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


      val compiler = new ScalaCompiler(settings, ctx)
      val run = new compiler.Run
      run.compile(command.files)

      timer.stop()

      compiler.leonExtraction.setImports(compiler.saveImports.imports )

      compiler.leonExtraction.compiledProgram match {
        case Some(pgm) =>
          pgm

        case None =>
          ctx.reporter.fatalError("Failed to extract Leon program.")
      }
    } else {
      ctx.reporter.fatalError("No input program.")
    }
  }
}
