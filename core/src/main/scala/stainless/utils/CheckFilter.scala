/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package utils

/** Filter functions / classes for verification purposes */
trait CheckFilter {

  val ctx: inox.Context

  private lazy val functions: Option[Seq[String]] = ctx.options.findOption(optFunctions)

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

  /** Same as below. Note the _ <: ... tricks because Set are invariant. */
  def shouldBeChecked(fid: Identifier, flags: Set[_ <: inox.ast.Trees#Flag]): Boolean = functions match {
    case None =>
      val isLibrary = flags map { _.name } contains "library"
      val isUnchecked = flags map { _.name } contains "unchecked"
      !(isLibrary || isUnchecked)

    case Some(funs) =>
      val fullName = fixedFullName(fid)
      funs exists { f => fullName endsWith f }
  }

  /** Checks whether the given function/class should be verified at some point. */
  def shouldBeChecked(fd: extraction.xlang.trees.FunDef): Boolean = shouldBeChecked(fd.id, fd.flags)

  // Invariants are already extracted to functions, so no need to process the class unless it's a dependency.
  def shouldBeChecked(cd: extraction.xlang.trees.ClassDef): Boolean = false

}

