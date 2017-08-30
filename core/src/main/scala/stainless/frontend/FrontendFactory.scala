/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

import java.io.File
import java.nio.file.{ Files, StandardCopyOption }

/** A Frontend factory which takes as input: context + compiler arguments + callback */
trait FrontendFactory {
  def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend

  protected val extraCompilerArguments: Seq[String] = Nil
  val libraryFiles: Seq[String]

  /** All the arguments for the underlying compiler. */
  protected def allCompilerArguments(compilerArgs: Seq[String]): Seq[String] =
    extraCompilerArguments ++ libraryFiles ++ compilerArgs
}

