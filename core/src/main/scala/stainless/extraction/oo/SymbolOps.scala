/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

trait SymbolOps extends imperative.SymbolOps { self: TypeOps =>
  import trees._
  import symbols._

  override def conditionForPatternRecImpl[P <: PathLike[P]]
               (in: Expr, pattern: Pattern)
               (implicit pp: PathProvider[P], bind: (Option[ValDef], Expr) => P): P = pattern match {
    case ClassPattern(b, ct, subPatterns) =>
      def accessField(id: Identifier) = ClassSelector(asInstOf(in, ct), id)
      val subTests = (ct.tcd.fields zip subPatterns) map { case (f, p) =>
        conditionForPatternRecImpl(accessField(f.id), p)(pp, bind)
      }
      pp.empty withCond isInstOf(in, ct) merge bind(b, asInstOf(in, ct)) merge subTests

    case _ =>
      super.conditionForPatternRecImpl(in, pattern)(pp, bind)
  }

}
