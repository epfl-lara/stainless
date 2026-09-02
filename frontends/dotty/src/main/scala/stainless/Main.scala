/* Copyright 2009-2026 EPFL, Lausanne */

package stainless

object Main extends MainHelpers {

  // Stainless is compiled with the same compiler it bundles as its frontend.
  val compilerVersion: String = BuildInfo.scalaVersion

  override protected def displayVersion(reporter: inox.Reporter): Unit = {
    super.displayVersion(reporter)
    reporter.info(s"Bundled Scala compiler: $compilerVersion")
  }

  // The Stainless library sources are shipped as resources, along with an index file
  // listing them (both emitted by the resource generator in build.sbt).
  private val libraryPaths: Seq[String] = {
    val stream = getClass.getClassLoader.getResourceAsStream("stainless/libfiles.txt")
    if (stream == null) sys.error("Missing resource stainless/libfiles.txt: the Stainless library index was not packaged with this build")
    val source = scala.io.Source.fromInputStream(stream)
    try source.getLines().toList finally source.close()
  }

  override val factory = new frontends.dotc.DottyCompiler.Factory(Nil, libraryPaths)

}
