/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import java.io.File
import java.nio.file.{ Files, StandardCopyOption }

/** A Frontend factory which takes as input: context + compiler arguments + callback */
trait FrontendFactory {
  def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend

  protected val extraCompilerArguments: Seq[String] = Nil
  protected val libraryPaths: Seq[String]

  private lazy val cl = getClass.getClassLoader

  /** Paths to the library files used by this frontend. */
  final lazy val libraryFiles: Seq[String] = libraryPaths.map  { libPath =>
    // There are two run modes: either the library is not packaged in a jar, and therefore
    // directly available as is from the disk, or it is embedded in stainless' jar file, in
    // which case we need to extract the files to a temporary location in order to let the
    // underlying compiler read them.

    // we replace `\` by `/` for windows because `getResource` (called later) expects `/`
    // this can be unsafe for strange file names (e.g. containing `\` on linux/mac)
    val url = cl.getResource(libPath.replace('\\', '/'))
    val path = url.getFile
    val file = new File(path)

    if (file.exists && file.isFile) file.getPath()
    else {
      // JAR URL syntax: jar:<url>!/{filepath}, Expected path syntax: file:/path/a.jar!/{filepath}
      assert(path startsWith "file:")
      val Array(_, filepath) = path split "!/"

      // Path should always use '/' as a separator (because of the replacement above in `getResource`)
      val filename = filepath.replace("/", "_")
      val splitPos = filename lastIndexOf '.'
      val (prefix, suffix) = filename splitAt splitPos
      val tmpFilePath = Files.createTempFile(prefix, suffix)
      val stream = url.openStream()
      Files.copy(stream, tmpFilePath, StandardCopyOption.REPLACE_EXISTING)
      stream.close()
      tmpFilePath.toFile.deleteOnExit()
      tmpFilePath.toString
    }
  }

  protected def extraSourceFiles(ctx: inox.Context): Seq[String] = {
    val extraDeps = ctx.options.findOptionOrDefault(optExtraDeps)
    val extraResolvers = ctx.options.findOptionOrDefault(optExtraResolvers)

    val resolver = new DependencyResolver(ctx, extraResolvers)
    resolver.fetchAll(extraDeps)
  }

  /** All the arguments for the underlying compiler. */
  protected def allCompilerArguments(ctx: inox.Context, compilerArgs: Seq[String]): Seq[String] = {
    val extraSources = extraSourceFiles(ctx)
    extraCompilerArguments ++ libraryFiles ++ extraSources ++ compilerArgs
  }
}

