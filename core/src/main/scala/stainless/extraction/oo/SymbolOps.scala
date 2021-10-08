/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait SymbolOps extends TypeOps with innerfuns.SymbolOps { self =>
  import trees._
  import symbols.{given, _}

  /** Converts the pattern applied to an input to a map between identifiers and expressions */
  override def mapForPattern(in: Expr, pattern: Pattern): Map[ValDef, Expr] = {
    def bindIn(vd: Option[ValDef], tpe: Type): Map[ValDef,Expr] = vd match {
      case None => Map()
      case Some(vd) => Map(vd -> AsInstanceOf(in, tpe).copiedFrom(in))
    }

    pattern match {
      case ClassPattern(b, ct, subps) =>
        assert(ct.tcd.fields.size == subps.size)

        val pairs = ct.tcd.fields zip subps
        val subMaps = pairs.map { p =>
          mapForPattern(ClassSelector(AsInstanceOf(in, ct), p._1.id), p._2)
        }
        val together = subMaps.flatten.toMap
        bindIn(b, ct) ++ together

      case InstanceOfPattern(b, ct) =>
        bindIn(b, ct)

      case _ => super.mapForPattern(in, pattern)
    }
  }

  protected class OOPatternConditions[P <: PathLike[P]](includeBinders: Boolean)(using pp: PathProvider[P])
    extends PatternConditions[P](includeBinders) {

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

  override protected def patternConditions[P <: PathLike[P]](includeBinders: Boolean)(using PathProvider[P]) =
    new OOPatternConditions[P](includeBinders)

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

  override def debugString(filter: String => Boolean)(using PrinterOptions): String = {
    super.debugString(filter) ++
    wrapWith("Classes", objectsToString(classes.values, filter)) ++
    wrapWith("Type definitions", objectsToString(typeDefs.values, filter))
  }

}
