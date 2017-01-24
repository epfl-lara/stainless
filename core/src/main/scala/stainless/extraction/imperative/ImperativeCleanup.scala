/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

/** Cleanup the program after running imperative desugaring.
  *
  * This functions simplifies away typical pattern of expressions
  * that can be generated during xlang desugaring phase. The most
  * common case is the generation of function returning tuple with
  * Unit in it, which can be safely eliminated.
  */
trait ImperativeCleanup extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: innerfuns.Trees

  def transform(syms: s.Symbols): t.Symbols = {
    implicit val symbols = syms

    val checkedSyms: t.Symbols = {
      object checker extends {
        val s: self.s.type = self.s
        val t: self.t.type = self.t
      } with CheckingTransformer {
        override def transform(tpe: s.Type): t.Type = tpe match {
          case s.TypeParameter(id, flags) if flags contains s.IsMutable =>
            t.TypeParameter(id, (flags - s.IsMutable) map transform).copiedFrom(tpe)
          case _ => super.transform(tpe)
        }

        override def transform(vd: s.ValDef): t.ValDef = {
          val (newId, newTpe) = transform(vd.id, vd.tpe)
          t.ValDef(newId, newTpe, (vd.flags - s.IsVar) map transform).copiedFrom(vd)
        }
      }

      t.NoSymbols
        .withADTs(syms.adts.values.toSeq.map(checker.transform))
        .withFunctions(syms.functions.values.toSeq.map { fd =>
          checker.transform(fd.copy(flags = fd.flags - s.IsPure))
        })
    }

    val pureUnitSyms: t.Symbols = {
      import self.t._
      import checkedSyms._

      object pureUnits extends SelfTreeTransformer {
        override def transform(e: Expr): Expr = e match {
          case tu @ Tuple(es) => Tuple(es.map {
            case IsTyped(e, UnitType) =>
              val te = transform(e)
              if (isPure(te)) UnitLiteral().copiedFrom(te) else te
            case e => transform(e)
          }).copiedFrom(tu)

          case _ => super.transform(e)
        }
      }

      t.NoSymbols
        .withADTs(checkedSyms.adts.values.toSeq.map(pureUnits.transform))
        .withFunctions(checkedSyms.functions.values.toSeq.map(pureUnits.transform))
    }

    val simpleSyms = t.NoSymbols
      .withADTs(pureUnitSyms.adts.values.toSeq)
      .withFunctions(pureUnitSyms.functions.values.toSeq.map { fd =>
        fd.copy(fullBody = pureUnitSyms.simplifyLets(fd.fullBody))
      })

    /*
    for (fd <- simpleSyms.functions.values) {
      import simpleSyms._
      if (fd.fullBody.getType == t.Untyped) {
        println(explainTyping(fd.fullBody)(t.PrinterOptions(symbols = Some(simpleSyms), printUniqueIds = true)))
      }
    }
    */

    simpleSyms
  }
}

