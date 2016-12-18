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

    object transformer extends {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    } with inox.ast.TreeTransformer {
      override def transform(tpe: s.Type): t.Type = tpe match {
        case s.TypeParameter(id, flags) if flags contains s.IsMutable =>
          t.TypeParameter(id, (flags - s.IsMutable) map transform).copiedFrom(tpe)
        case s.TupleType(bases) =>
          t.tupleTypeWrap(bases map transform filterNot (_ == t.UnitType)).copiedFrom(tpe)
        case _ => super.transform(tpe)
      }

      override def transform(e: s.Expr): t.Expr = e match {
        case sel @ s.TupleSelect(s.IsTyped(tpl, s.TupleType(bases)), index) =>
          val realBases = bases map transform
          if (realBases(index - 1) == t.UnitType) {
            t.UnitLiteral()
          } else {
            val nbUnitsUntilIndex = realBases.take(index).count(_ == t.UnitType)
            val nbNonUnitsTotal = realBases.count(_ != t.UnitType)
            if (nbUnitsUntilIndex == 0) super.transform(e)
            else if (nbNonUnitsTotal == 1) transform(tpl)
            else t.TupleSelect(transform(tpl), index - nbUnitsUntilIndex).copiedFrom(sel)
          }

        case tu @ s.Tuple(es) =>
          val realTypes = es.map(_.getType) map transform
          if (realTypes exists (_ == t.UnitType)) {
            t.tupleWrap((es zip realTypes).filter(p => p._2 != t.UnitType).map(p => transform(p._1))).copiedFrom(tu)
          } else {
            super.transform(tu)
          }

        case _ => super.transform(e)
      }

      override def transform(vd: s.ValDef): t.ValDef = {
        val (newId, newTpe) = transform(vd.id, vd.tpe)
        t.ValDef(newId, newTpe, (vd.flags - s.IsVar) map transform).copiedFrom(vd)
      }
    }

    val untupledSyms = t.NoSymbols
      .withADTs(syms.adts.values.toSeq.map(transformer.transform))
      .withFunctions(syms.functions.values.toSeq.map { fd =>
        transformer.transform(fd.copy(flags = fd.flags - s.IsPure))
      })

    val simpleSyms = t.NoSymbols
      .withADTs(untupledSyms.adts.values.toSeq)
      .withFunctions(untupledSyms.functions.values.toSeq.map { fd =>
        fd.copy(fullBody = untupledSyms.simplifyLets(fd.fullBody))
      })

    /*
    for (fd <- simpleSyms.functions.values) {
      import simpleSyms._
      if (fd.fullBody.getType == t.Untyped) {
        println(explainTyping(fd.fullBody)(t.PrinterOptions(symbols = Some(simpleSyms), printUniqueIds = true)))
      }
      println(fd)
    }
    */

    simpleSyms
  }
}

