/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

trait PreconditionInference extends inox.ast.SymbolTransformer { self =>
  val trees: Trees
  lazy val s: trees.type = trees
  lazy val t: trees.type = trees

  import trees._

  def transform(symbols: Symbols): Symbols = {
    import symbols._

    val preRefs: Map[Identifier, Boolean] = {
      def initRefs = symbols.functions.values.map(fd => fd -> exprOps.exists {
        case Pre(_) => true
        case _ => false
      } (fd.fullBody)).toMap

      initRefs.map { case (fd, hasPre) =>
        fd.id -> (hasPre || transitiveCallees(fd).exists(fd => initRefs(fd)))
      }
    }

    val newFunctions = (for (fd <- symbols.functions.values) yield {
      if (!exprOps.exists {
        case Pre(_) => true
        case FunctionInvocation(id, _, _) => preRefs(id)
        case _ => false
      } (fd.precOrTrue)) {
        val preExtensions = fd.params.flatMap(vd => vd.tpe match {
          case FunctionType(from, to) if from.nonEmpty =>
            val vds = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
            Some(funRequires(vd.toVariable, Lambda(vds, BooleanLiteral(true))))
          case _ =>
            None
        })

        if (preExtensions.nonEmpty) {
          val newPre = andJoin(fd.precondition.toSeq ++ preExtensions)
          fd.copy(fullBody = exprOps.withPrecondition(fd.fullBody, Some(newPre)))
        } else {
          fd
        }
      } else {
        fd
      }
    }).toSeq

    NoSymbols.withADTs(symbols.adts.values.toSeq).withFunctions(newFunctions)
  }
}
