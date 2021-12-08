/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

trait Definitions extends methods.Trees { self: Trees =>

  case class LocalClassDef(
    id: Identifier,
    tparams: Seq[TypeParameterDef],
    parents: Seq[Type],
    fields: Seq[ValDef],
    methods: Seq[LocalMethodDef],
    typeMembers: Seq[LocalTypeDef],
    flags: Seq[Flag]
  ) extends Definition {

    def globalAncestors(using s: Symbols): Seq[TypedClassDef] = {
      val allAncestors = parents
        .flatMap {
          case ct: ClassType => ct.lookupClass
          case _ => None
        }
        .flatMap(tcd => tcd +: tcd.ancestors)

      val typedMap = allAncestors.groupBy(_.cd).map { case (cd, tcds) =>
        val tps = cd.typeArgs.zipWithIndex.map { case (tp, i) =>
          val insts @ (head +: tail) = tcds.map(_.tps(i))
          if (tp.isCovariant) s.greatestLowerBound(insts)
          else if (tp.isContravariant) s.leastUpperBound(insts)
          else if (tail.forall(_ == head)) head
          else Untyped
        }

        cd -> cd.typed(tps)
      }
      allAncestors.map(_.cd).distinct.map(typedMap)
    }

    def typeArgs = tparams map (_.tp)
  }

  object LocalClassDef {
    // Note: Only to be used during extraction from Scala/Dotty trees
    def apply(cd: ClassDef, methods: Seq[FunDef], typeMembers: Seq[TypeDef]): LocalClassDef = {
      LocalClassDef(
        cd.id, cd.tparams, cd.parents, cd.fields,
        methods.map(LocalMethodDef(_)),
        typeMembers.map(LocalTypeDef(_)),
        cd.flags
      ).copiedFrom(cd)
    }
  }

  case class LocalMethodDef(
    id: Identifier,
    tparams: Seq[TypeParameterDef],
    params: Seq[ValDef],
    returnType: Type,
    fullBody: Expr,
    flags: Seq[Flag]
  ) extends Definition {
    def toFunDef: FunDef = new FunDef(id, tparams, params, returnType, fullBody, flags).copiedFrom(this)
  }

  object LocalMethodDef {
    // Note: Only to be used during extraction from Scala/Dotty trees
    def apply(fd: FunDef): LocalMethodDef =
      LocalMethodDef(fd.id, fd.tparams, fd.params, fd.returnType, fd.fullBody, fd.flags).copiedFrom(fd)
  }

  case class LocalTypeDef(
    id: Identifier,
    tparams: Seq[TypeParameterDef],
    rhs: Type,
    flags: Seq[Flag],
  ) extends Definition {
    def toTypeDef: TypeDef = new TypeDef(id, tparams, rhs, flags).copiedFrom(this)
  }

  object LocalTypeDef {
    // Note: Only to be used during extraction from Scala/Dotty trees
    def apply(td: TypeDef): LocalTypeDef =
      LocalTypeDef(td.id, td.tparams, td.rhs, td.flags).copiedFrom(td)
  }
}
