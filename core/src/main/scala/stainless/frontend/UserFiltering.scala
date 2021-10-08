/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import extraction._
import xlang.{ trees => xt }

import stainless.utils.CheckFilter

class UserFiltering private(override val s: xt.type,
                            override val t: xt.type,
                            override val trees: xt.type)
                           (using val context: inox.Context)
  extends inox.transformers.SymbolTransformer with CheckFilter {

  def this()(using inox.Context) = this(xt, xt, xt)

  import trees._
  import exprOps._

  override def transform(symbols: s.Symbols): t.Symbols = {
    def notUserFlag(f: xt.Flag) = f.name == "library" || f == xt.Synthetic

    val userIds =
      symbols.classes.values.filterNot(cd => cd.flags.exists(notUserFlag)).map(_.id) ++
      symbols.functions.values.filterNot(fd => fd.flags.exists(notUserFlag)).filter(isInOptions).map(_.id) ++
      symbols.typeDefs.values.filterNot(td => td.flags.exists(notUserFlag)).map(_.id)

    val userDependencies = (userIds.flatMap(symbols.dependencies) ++ userIds).toSeq
    val keepGroups = context.options.findOptionOrDefault(optKeep)

    def hasKeepFlag(flags: Seq[xt.Flag]) =
      flags.exists(_.name == "keep") ||
      keepGroups.exists(g => flags.contains(xt.Annotation("keepFor", Seq(xt.StringLiteral(g)))))

    def keepDefinition(defn: xt.Definition): Boolean =
      hasKeepFlag(defn.flags) || userDependencies.contains(defn.id)

    xt.NoSymbols.withClasses(symbols.classes.values.filter(keepDefinition).toSeq)
                .withFunctions(symbols.functions.values.filter(keepDefinition).toSeq)
                .withTypeDefs(symbols.typeDefs.values.filter(keepDefinition).toSeq)
  }

}
