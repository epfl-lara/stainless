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
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {

    object transformer extends {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    } with TreeTransformer {
      def transform(tpe: s.Type): t.Type = tpe match {
        case s.TupleType(bases) =>
          t.tupleTypeWrap(bases map transform filterNot (_ == t.UnitType))
        case _ => super.transform(tpe)
      }

      def transform(e: s.Expr): t.Expr = e match {
        case sel @ TupleSelect(IsTyped(tpl, TupleType(bases)), index) =>
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

        case tu @ Tuple(es) =>
          val realTypes = es.map(_.getType) map transform
          if (realTypes exists (_ == t.UnitType)) {
            tupleWrap((es zip realTypes).filter(p => p._2 != t.UnitType).map(_._1)).copiedFrom(tu)
          } else {
            super.transform(tu)
          }

        case _ => super.transform(e)
      }
    }

    syms.transform(transformer)
  }
}

