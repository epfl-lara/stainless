/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

trait SymbolOps extends imperative.SymbolOps { self: TypeOps =>
  import trees._
  import symbols._

  protected class PatternConditions[P <: PathLike[P]](includeBinders: Boolean)(implicit pp: PathProvider[P])
    extends super.PatternConditions[P](includeBinders) {

    override def apply(in: Expr, pattern: Pattern): P = pattern match {
      case ClassPattern(b, ct, subPatterns) =>
        def accessField(id: Identifier) = ClassSelector(asInstOf(in, ct), id)
        val subTests = (ct.tcd.fields zip subPatterns) map { case (f, p) => apply(accessField(f.id), p) }
        pp.empty withCond isInstOf(in, ct) merge bind(b, asInstOf(in, ct)) merge subTests

      case InstanceOfPattern(ob, ct: ClassType) =>
        pp.empty withCond isInstOf(in, ct) merge bind(ob, in)

      case _ => super.apply(in, pattern)
    }
  }

  override protected def patternConditions[P <: PathLike[P]](includeBinders: Boolean)
                                                            (implicit pp: PathProvider[P]) = 
                                                              new PatternConditions[P](includeBinders)

}
