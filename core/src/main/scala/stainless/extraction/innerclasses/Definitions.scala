/* Copyright 2009-2018 EPFL, Lausanne */

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
    flags: Seq[Flag]
  ) extends Definition {

    def globalAncestors(implicit s: Symbols): Seq[TypedClassDef] = {
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
    def apply(cd: ClassDef, methods: Seq[FunDef]): LocalClassDef = {
      LocalClassDef(cd.id, cd.tparams, cd.parents,
        cd.fields, methods.map(LocalMethodDef(_)), cd.flags).copiedFrom(cd)
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
}
