/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package utils

/** Filter functions for verification purposes. */
trait CheckFilter {
  protected val context: inox.Context
  protected val trees: ast.Trees
  import trees._

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

  private lazy val pathsOpt: Option[Seq[Path]] = context.options.findOption(optFunctions) map { functions =>
    functions map fullNameToPath
  }

  private def shouldBeChecked(fid: Identifier, flags: Seq[trees.Flag]): Boolean = pathsOpt match {
    case None =>
      val isLibrary = flags exists (_.name == "library")
      val isUnchecked = flags contains Unchecked
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

  def filter(ids: Seq[Identifier], symbols: trees.Symbols, component: Component): Seq[Identifier] = {
    def isDerivedFrom(ids: Set[Identifier])(fd: trees.FunDef): Boolean =
      fd.flags.exists { case trees.Derived(id) => ids(id) case _ => false }

    val init = ids.flatMap(id => symbols.lookupFunction(id).toSeq).filter(shouldBeChecked).map(_.id).toSet

    val toCheck = inox.utils.fixpoint { (ids: Set[Identifier]) =>
      ids ++ symbols.functions.values.toSeq
        .filter(isDerivedFrom(ids))
        .filter(shouldBeChecked)
        .map(_.id)
    } (init)

    val toProcess = toCheck.toSeq.sortBy(symbols.getFunction(_).getPos)

    for (id <- toProcess) {
      val fd = symbols.getFunction(id)
      if (fd.flags exists (_.name == "library")) {
        val fullName = fd.id.fullName
        context.reporter.warning(
          s"Component [${component.name}]: Forcing processing of $fullName which was assumed verified")
      }
    }

    toProcess
  }

  /** Checks whether the given function/class should be verified at some point. */
  def shouldBeChecked(fd: FunDef): Boolean =
    shouldBeChecked(fd.id, fd.flags)
}

object CheckFilter {
  def apply(t: ast.Trees, ctx: inox.Context): CheckFilter {
    val trees: t.type
  } = new CheckFilter {
    override val context = ctx
    override val trees: t.type = t
  }
}

