package stainless
package utils

import stainless.extraction.xlang.{trees => xt}

object LibraryFilter {

  private def shouldRemoveLibraryFlag(fn: xt.FunDef, symbols: xt.Symbols): Boolean = {
    import symbols.given

    if (fn.flags.contains(xt.Synthetic) || !fn.isLibrary || !fn.isLaw)
      false
    else {
      val optClass = fn.getClassDef

      optClass match {
        case None => false
        case Some(cd) =>
          (for {
            subclass <- cd.descendants

            // Check if subclass is not library
            if !subclass.isLibrary

            // Check if the subclass doesn't override the method with one that is specifically flagged as library
            if !subclass.methods.map(symbols.getFunction).exists(subFn =>
                  subFn.id.name == fn.id.name && subFn.isLibrary)
          } yield subclass).nonEmpty
      }
    }
  }

  def removeLibraryFlag(symbols: xt.Symbols): xt.Symbols = {
    val funsToRemoveLibrary: Set[Identifier] =
      (for {
        fd <- symbols.functions.values
        if shouldRemoveLibraryFlag(fd, symbols)
      } yield fd.id).toSet

    def removeLibrary(fd: xt.FunDef): xt.FunDef =
      if (funsToRemoveLibrary.contains(fd.id))
        fd.copy(flags = fd.flags.filterNot(_.name == "library"))
      else
        fd

    val currentClasses = symbols.classes.values.toSeq
    val currentFunctions = symbols.functions.values.toSeq.map(removeLibrary)
    val currentTypeDefs = symbols.typeDefs.values.toSeq

    xt.NoSymbols
      .withClasses(currentClasses)
      .withFunctions(currentFunctions)
      .withTypeDefs(currentTypeDefs)
  }
}