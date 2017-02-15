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
        def requires(e: Expr): Expr = e.getType match {
          case FunctionType(from, to) =>
            val vds = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
            val req = if (from.nonEmpty) {
              funRequires(e, Lambda(vds, BooleanLiteral(true)))
            } else {
              BooleanLiteral(true)
            }
            and(req, forall(vds, requires(application(e, vds.map(_.toVariable)))))

          case TupleType(tps) =>
            andJoin(tps.indices.map(i => requires(TupleSelect(e, i + 1))))

          case adt: ADTType => adt.getADT match {
            case tadt if tadt.definition.isInductive => BooleanLiteral(true)
            case tcons: TypedADTConstructor =>
              andJoin(tcons.fields.map(vd => requires(ADTSelector(e, vd.id))))

            case tsort: TypedADTSort =>
              andJoin(tsort.constructors.map { tcons =>
                Implies(IsInstanceOf(e, tcons.toType), requires(AsInstanceOf(e, tcons.toType)))
              })
          }

          case _ => BooleanLiteral(true)
        }

        val preExtension = andJoin(fd.params.map(vd => requires(vd.toVariable)))

        if (preExtension != BooleanLiteral(true)) {
          val newPre = andJoin(preExtension +: fd.precondition.toSeq)
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
