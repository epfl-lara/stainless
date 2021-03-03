/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import extraction._
import xlang.{ trees => xt }

import stainless.utils.LibraryFilter

trait Preprocessing extends oo.CachingPhase
  with IdentityFunctions
  with IdentitySorts
  with oo.IdentityClasses
  with oo.IdentityTypeDefs {

  override val s: xt.type = xt
  override val t: xt.type = xt

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override def extractSymbols(ctx: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val initialSymbols = strictBVCleaner.transform(LibraryFilter.removeLibraryFlag(symbols))

    def notUserFlag(f: xt.Flag) = f.name == "library" || f == xt.Synthetic

    val userIds =
      initialSymbols.classes.values.filterNot(cd => cd.flags.exists(notUserFlag)).map(_.id) ++
      initialSymbols.functions.values.filterNot(fd => fd.flags.exists(notUserFlag)).map(_.id) ++
      initialSymbols.typeDefs.values.filterNot(td => td.flags.exists(notUserFlag)).map(_.id)

    val userDependencies = (userIds.flatMap(initialSymbols.dependencies) ++ userIds).toSeq
    val keepGroups = context.options.findOptionOrDefault(optKeep)

    def hasKeepFlag(flags: Seq[xt.Flag]) =
      flags.exists(_.name == "keep") ||
      keepGroups.exists(g => flags.contains(xt.Annotation("keepFor", Seq(xt.StringLiteral(g)))))

    def keepDefinition(defn: xt.Definition): Boolean =
      hasKeepFlag(defn.flags) || userDependencies.contains(defn.id)

    val preSymbols =
      xt.NoSymbols.withClasses(initialSymbols.classes.values.filter(keepDefinition).toSeq)
                  .withFunctions(initialSymbols.functions.values.filter(keepDefinition).toSeq)
                  .withTypeDefs(initialSymbols.typeDefs.values.filter(keepDefinition).toSeq)

    Recovery.recover(preSymbols)
  }

}

object Preprocessing {
  def apply()(implicit ctx: inox.Context) = new {
    override val context = ctx
  } with Preprocessing
}
