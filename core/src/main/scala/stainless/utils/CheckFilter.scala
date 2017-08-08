/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package utils

/** Filter functions / classes for verification purposes */
trait CheckFilter {

  val ctx: inox.Context

  type Path = Seq[String]
  private def fullNameToPath(fullName: String): Path = (fullName split '.').toSeq

  // TODO this is probably done somewhere else in a cleaner fasion...
  private def fixedFullName(id: Identifier): String = id.fullName
    .replaceAllLiterally("$bar", "|")
    .replaceAllLiterally("$up", "^")
    .replaceAllLiterally("$eq", "=")
    .replaceAllLiterally("$plus", "+")
    .replaceAllLiterally("$minus", "-")
    .replaceAllLiterally("$times", "*")
    .replaceAllLiterally("$div", "/")
    .replaceAllLiterally("$less", "<")
    .replaceAllLiterally("$geater", ">")
    .replaceAllLiterally("$colon", ":")
    .replaceAllLiterally("$amp", "&")
    .replaceAllLiterally("$tilde", "~")

  private lazy val pathsOpt: Option[Seq[Path]] = ctx.options.findOption(optFunctions) map { functions =>
    functions map fullNameToPath
  }

  /** Same as below. Note the _ <: ... tricks because Set are invariant. */
  def shouldBeChecked(fid: Identifier, flags: Set[_ <: inox.ast.Trees#Flag]): Boolean = pathsOpt match {
    case None =>
      val isLibrary = flags map { _.name } contains "library"
      val isUnchecked = flags map { _.name } contains "unchecked"
      !(isLibrary || isUnchecked)

    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumes.
      val path: Path = fullNameToPath(fixedFullName(fid))
      paths exists { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
  }

  /** Checks whether the given function/class should be verified at some point. */
  def shouldBeChecked(fd: extraction.xlang.trees.FunDef): Boolean = shouldBeChecked(fd.id, fd.flags)

  // Invariants are already extracted to functions, so no need to process the class unless it's a dependency.
  def shouldBeChecked(cd: extraction.xlang.trees.ClassDef): Boolean = false

}

