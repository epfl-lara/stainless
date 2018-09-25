/* Copyright 2009-2018 EPFL, Lausanne */

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

  /** $encodingof expr.asInstanceOf[tpe], returns `expr` if it already is of type `tpe`.  */
  def asInstOf(expr: Expr, tpe: Type) = {
    if (symbols.isSubtypeOf(expr.getType, tpe)) {
      expr
    } else {
      AsInstanceOf(expr, tpe).copiedFrom(expr)
    }
  }

  /** $encodingof expr.isInstanceOf[tpe], simplifies to `true` or `false` in clear cases. */
  def isInstOf(expr: Expr, tpe: Type) = (expr.getType, tpe) match {
    case (t1, t2) if symbols.isSubtypeOf(t1, t2) => BooleanLiteral(true).copiedFrom(expr)

    //case (t1: ADTType, t2: ADTType)
    //if t1.id != t2.id && !t1.getADT.definition.isSort && !t2.getADT.definition.isSort => BooleanLiteral(false).copiedFrom(expr)

    case _ => IsInstanceOf(expr, tpe).copiedFrom(expr)
  }

  override def symbolsToString(objs: Set[String])(implicit pOpts: PrinterOptions): String = {
    super.symbolsToString(objs) ++ wrapWith("Classes", objectsToString(classes.values, objs))
  }

}
