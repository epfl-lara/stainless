/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

import scala.collection.mutable.{Map => MutableMap}

trait Types extends inox.ast.Types { self: Trees =>

  class ClassType(id: Identifier, tps: Seq[Type]) extends ADTType(id, tps) {
    def lookupClass(implicit s: Symbols): Option[TypedClassDef] = s.lookupClass(id, tps)
    def tcd(implicit s: Symbols): TypedClassDef = s.getClass(id, tps)

    private[xlang] def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = {
      def rec(tcd: TypedClassDef): Option[ValDef] =
        tcd.fields.collectFirst { case vd @ ValDef(`selector`, _) => vd }.orElse(tcd.parent.flatMap(rec))
      lookupClass.flatMap(rec)
    }
  }

  object ClassType {
    def apply(id: Identifier, tps: Seq[Type]): ClassType = new ClassType(id, tps)
    def unapply(tpe: Type): Option[(Identifier, Seq[Type])] = tpe match {
      case ct: ClassType => Some((ct.id, ct.tps))
      case _ => None
    }
  }
}

trait TypeOps extends ast.TypeOps {
  protected val trees: Trees
  import trees._

  override def typeBound(t1: Type, t2: Type, isLub: Boolean, allowSub: Boolean)
                        (implicit freeParams: Seq[TypeParameter]): Option[(Type, Map[TypeParameter, Type])] = {
    (t1, t2) match {
      case (ct: ClassType, _) if !ct.lookupClass.isDefined => None
      case (_, ct: ClassType) if !ct.lookupClass.isDefined => None

      case (ct1: ClassType, ct2: ClassType) =>
        val cd1 = ct1.tcd.cd
        val cd2 = ct2.tcd.cd
        val bound: Option[ClassDef] = if (allowSub) {
          val an1 = cd1 +: cd1.ancestors
          val an2 = cd2 +: cd2.ancestors
          if (isLub) {
            (an1.reverse zip an2.reverse)
              .takeWhile(((_: ClassDef) == (_: ClassDef)).tupled)
              .lastOption.map(_._1)
          } else {
            if (an1.contains(cd2)) Some(cd1)
            else if (an2.contains(cd1)) Some(cd2)
            else None
          }
        } else {
          if (cd1 == cd2) Some(cd1) else None
        }

        for {
          cd <- bound
          (subs, map) <- flattenTypeMappings((ct1.tps zip ct2.tps).map { case (tp1, tp2) =>
            typeBound(tp1, tp2, isLub, allowSub = false)
          })
        } yield (cd.typed(subs).toType, map)

      case _ => super.typeBound(t1, t2, isLub, allowSub)
    }
  }
  
}
