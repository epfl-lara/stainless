/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

trait Types extends methods.Trees { self: Trees =>

  case class LocalClassType(
    id: Identifier,
    tparams: Seq[TypeParameterDef],
    tps: Seq[Type],
    ancestors: Seq[Type]
  ) extends Type {
    def toClassTypeAbs(implicit syms: Symbols): ClassTypeAbs = ClassTypeAbs(this)
    def toClassType: ClassType = ClassType(id, tps)
  }

  sealed abstract class ClassTypeAbs(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val tps: Seq[Type],
    val allAncestors: Seq[ClassTypeAbs],
    val underlying: Type
  ) extends Type {
    def typeArgs: Seq[TypeParameter] = tparams.map(_.tp)
    def ancestors(implicit s: Symbols): Seq[ClassTypeAbs]
    def applied(tps: Seq[Type]): ClassTypeAbs
  }

  object ClassTypeAbs {
    def apply(tp: Type)(implicit s: Symbols): ClassTypeAbs = tp match {
      case l: LocalClassType => Local(l)
      case g: ClassType => Global(g)
    }

    case class Local(lct: LocalClassType)(implicit s: Symbols)
      extends ClassTypeAbs(lct.id, lct.tparams, lct.tps,
        lct.ancestors.map(ClassTypeAbs(_)), lct) {

      override def ancestors(implicit s: Symbols): Seq[ClassTypeAbs] = {
        val subst = typeArgs.zip(tps).toMap
        val typedMap = allAncestors.groupBy(_.id).map { case (id, cts) =>
          val tps = cts.head.typeArgs.zipWithIndex.map { case (tp, i) =>
            val preInsts = cts.map(_.tps(i))
            val insts @ (head +: tail) = preInsts.map(i => typeOps.instantiateType(i, subst))
            if (tp.isCovariant) s.greatestLowerBound(insts)
            else if (tp.isContravariant) s.leastUpperBound(insts)
            else if (tail.forall(_ == head)) head
            else Untyped
          }

          id -> cts.head.applied(tps)
        }

        allAncestors.distinct.map(ct => typedMap(ct.id))
      }

      override def applied(tps: Seq[Type]): ClassTypeAbs = Local(lct.copy(tps = tps))
      override def asString(implicit popts: PrinterOptions): String = lct.asString
    }

    case class Global(ct: ClassType)(implicit s: Symbols)
      extends ClassTypeAbs(ct.id, ct.tcd.cd.tparams, ct.tps,
        ct.tcd.ancestors.map(a => ClassTypeAbs(a.toType)), ct) {

      override def ancestors(implicit s: Symbols): Seq[ClassTypeAbs] = allAncestors
      override def applied(tps: Seq[Type]): ClassTypeAbs = Global(ct.copy(tps = tps))
      override def asString(implicit popts: PrinterOptions): String = ct.asString
    }
  }

}
