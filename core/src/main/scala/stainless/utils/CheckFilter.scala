/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

/** Filter functions for verification purposes. */
trait CheckFilter {
  protected val context: inox.Context
  protected val trees: ast.Trees
  import trees._

  type Path = Seq[String]

  private lazy val pathsOpt: Option[Seq[Path]] = context.options.findOption(optFunctions) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  def isInOptions(fid: Identifier): Boolean = pathsOpt match {
    case None => true
    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumes.
      pathsOpt.isEmpty
      val path: Path = CheckFilter.fullNameToPath(CheckFilter.fixedFullName(fid))
      paths exists { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
  }

  private def shouldBeChecked(fid: Identifier, flags: Seq[trees.Flag]): Boolean = {
    val isUnchecked = flags.contains(DropVCs)
    pathsOpt match {
      case None =>
        val isLibrary = flags exists (_.name == "library")
        val isUnchecked = flags contains DropVCs
        !(isLibrary || isUnchecked)

      case Some(paths) => !isUnchecked && isInOptions(fid)
    }
  }

  def filter(ids: Seq[Identifier], symbols: trees.Symbols, component: Component): Seq[Identifier] = {
    def isDerivedFrom(ids: Set[Identifier])(fd: trees.FunDef): Boolean =
      fd.flags.exists {
        case trees.Derived(Some(id)) => ids(id)
        case trees.Derived(None) => true
        case _ => false
      }
    val keptFromIds = ids.flatMap(id => symbols.lookupFunction(id).toSeq).filter(shouldBeChecked).map(_.id).toSet
    // Computes all transitively derived functions (values) from a given one (key)
    // NOTE: `fixpoint` is a generic utility and uses equality to determine whether we have reached a fixpoint
    // Consider a more optimized solution if this causes significant slowdowns.
    val derivedFrom = inox.utils.fixpoint { (acc: Map[Identifier, Set[Identifier]]) =>
      symbols.functions.values.foldLeft(acc) {
        case (acc, fd) =>
          val origins = fd.flags.flatMap {
            case trees.Derived(Some(orig)) => Some(orig)
            case _ => None
          }.toSet
          val transitiveOrigins = origins ++ acc.filter(_._2.intersect(origins).nonEmpty).keySet
          transitiveOrigins.foldLeft(acc) {
            case (acc, origin) => acc.updatedWith(origin)(_.map(_ + fd.id).orElse(Some(Set(fd.id))))
          }
      }
    } (Map.empty)

    // Take all functions that are derived from the ones found in `ids` and that should be checked for.
    // This takes care of inner functions.
    // Note that `ids` comes from syms.function where the `syms` are *before* the lowering phase
    // and filtered according to `UserFiltering`.
    // This means in particular that inner functions are not hoisted and will not be contained in `ids`.
    // Here, the symbols are the lowered one, so the inner functions are hoisted and contained in `symbols.function`
    // `UserFiltering` will also make sure to go through the definition of the (outer) functions
    // and include those that contain at least one inner function that should be kept (according to --functions)
    val derivedKept = ids.flatMap(derivedFrom.getOrElse(_, Set.empty).filter(derived => shouldBeChecked(symbols.functions(derived))))
    val init = keptFromIds ++ derivedKept

    val toCheck = inox.utils.fixpoint { (ids: Set[Identifier]) =>
      // Note that we do not filter derived functions and always consider them
      // for checking since the user is expecting these to be checked
      // (e.g. when checking for a function containing a while loop, the
      // function derived from the while loop should also be checked).
      ids ++ symbols.functions.values.toSeq
        .filter(isDerivedFrom(ids))
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
  def shouldBeChecked(fd: FunDef): Boolean = shouldBeChecked(fd.id, fd.flags)

  def isInOptions(fd: FunDef): Boolean = isInOptions(fd.id)

}

object CheckFilter {
  def apply(t: ast.Trees, ctx: inox.Context): CheckFilter {
    val trees: t.type
  } = new CheckFilter {
    override val context = ctx
    override val trees: t.type = t
  }

  type Path = Seq[String]

  def fullNameToPath(fullName: String): Path = (fullName split '.').toSeq

  // TODO this is probably done somewhere else in a cleaner fasion...
  def fixedFullName(id: Identifier): String = id.fullName
    .replace("$bar", "|")
    .replace("$up", "^")
    .replace("$eq", "=")
    .replace("$plus", "+")
    .replace("$minus", "-")
    .replace("$times", "*")
    .replace("$div", "/")
    .replace("$less", "<")
    .replace("$geater", ">")
    .replace("$colon", ":")
    .replace("$amp", "&")
    .replace("$tilde", "~")
}
