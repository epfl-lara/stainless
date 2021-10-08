/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import extraction.throwing.trees._

import collection.mutable.{ Set => MutableSet }

private[genc] object ExtraOps {
  // copied from AdtSpecialization
  def root(id: Identifier)(using symbols: Symbols): Identifier = {
    symbols.getClass(id).parents.map(ct => root(ct.id)).headOption.getOrElse(id)
  }

  val manualDefAnnotation = "cCode.function"

  extension (fa: FunAbstraction)  {
    def isManuallyDefined: Boolean = hasAnnotation(manualDefAnnotation)
    def isExtern: Boolean = fa.flags contains Extern
    def isDropped: Boolean = hasAnnotation("cCode.drop") || fa.flags.contains(Ghost)
    def isVal: Boolean = fa.isInstanceOf[Outer] && fa.asInstanceOf[Outer].fd.isVal

    def extAnnotations: Map[String, Seq[Any]] = fa.flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap
    def annotations: Set[String] = extAnnotations.keySet

    private def hasAnnotation(annot: String): Boolean = annotations contains annot
  }

  // Extra tools on FunDef, especially for annotations
  extension (fd: FunDef) {
    def isMain: Boolean = fd.id.name == "main"

    def isExtern: Boolean          = fd.flags contains Extern
    def isDropped : Boolean        = hasAnnotation("cCode.drop") || fd.flags.contains(Ghost)
    def isExported : Boolean       = hasAnnotation("cCode.export")
    def isManuallyDefined: Boolean = hasAnnotation(manualDefAnnotation)
    def isVal             =
      (fd.flags.exists(_.name == "accessor") || fd.flags.exists { case IsField(_) => true case _ => false }) &&
      fd.tparams.isEmpty && fd.params.isEmpty

    def extAnnotations: Map[String, Seq[Any]] = fd.flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap
    def annotations: Set[String] = extAnnotations.keySet

    def isGeneric = fd.tparams.length > 0

    def hasAnnotation(annot: String): Boolean = annotations contains annot
  }


  case class ManualType(alias: String, include: Option[String])

  private val manualTypeAnnotation = "cCode.typedef"
  private val droppedAnnotation = "cCode.drop"

  // Extra tools on ClassDef, especially for annotations, inheritance & generics
  extension (cd: ClassDef) {
    def isManuallyTyped: Boolean       = hasAnnotation(manualTypeAnnotation)
    def isDropped: Boolean             = hasAnnotation(droppedAnnotation)
    def isExported: Boolean            = hasAnnotation("cCode.export")
    def isPacked: Boolean              = hasAnnotation("cCode.pack")
    def isGlobal: Boolean              = cd.flags.exists(_.name.startsWith("cCode.global"))
    def isGlobalDefault: Boolean       = cd.flags.exists(_.name == "cCode.global")
    def isGlobalUninitialized: Boolean = cd.flags.exists(_.name == "cCode.globalUninitialized")
    def isGlobalExternal: Boolean      = cd.flags.exists(_.name == "cCode.globalExternal")

    def extAnnotations: Map[String, Seq[Any]] = cd.flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap
    def annotations: Set[String] = extAnnotations.keySet

    def getManualType: ManualType = {
      assert(isManuallyTyped)

      val Seq(StringLiteral(alias), StringLiteral(includes0)) = cd.extAnnotations(manualTypeAnnotation)
      val include = if (includes0.isEmpty) None else Some(includes0)

      ManualType(alias, include)
    }

    def isCandidateForInheritance: Boolean = cd.isAbstract || !cd.parents.isEmpty

    def isGeneric: Boolean = cd.tparams.length > 0

    def isRecursive(using Symbols): Boolean = {
      val defs: Set[ClassDef] = cd.parents.map(_.tcd.cd).toSet + cd

      val seens = MutableSet[ClassType]()

      def rec(typ: Type): Boolean = typ match {
        case t: ClassType if seens(t) => false

        case t: ClassType =>
          val cd0 = t.tcd.cd
          defs(cd0) || {
            seens += t

            (cd0.fields map { _.getType } exists rec) ||
            (cd0.parents exists rec) ||
            (cd0.children exists (cd => rec(cd.typed.toType)))
          }

        case NAryType(ts, _) => ts exists rec

        case _ => false
      }

      // Find out if the parent of cd or cd itself are involved in a type of a field
      cd.fields map { _.getType } exists rec
    }

    // copied from AdtSpecialization
    def isCandidate(using symbols: Symbols): Boolean = {
      val id = cd.id

      cd.parents match {
        case Nil =>
          def rec(cd: ClassDef): Boolean = {
            val cs = cd.children
            (cd.parents.size <= 1) &&
            (cd.typeMembers.isEmpty) &&
            (cs forall rec) &&
            (cd.parents forall (_.tps == cd.typeArgs)) &&
            ((cd.flags contains IsAbstract) || cs.isEmpty) &&
            (!(cd.flags contains IsAbstract) || cd.fields.isEmpty) &&
            (cd.typeArgs forall (tp => tp.isInvariant && !tp.flags.exists { case Bounds(_, _) => true case _ => false }))
          }
          rec(cd)
        case _ => symbols.getClass(root(id)).isCandidate
      }
    }

    // copied from AdtSpecialization
    def isCaseObject(using symbols: Symbols): Boolean = {
      val id = cd.id
      isCandidate && (symbols.getClass(id).flags contains IsCaseObject)
    }

    // Check whether the class has some fields or not
    def isEmpty: Boolean = cd.fields.isEmpty

    def hasAnnotation(annot: String): Boolean = cd.annotations contains annot
  }

  def isGlobal(tpe: Type)(using Symbols): Boolean = tpe match {
    case ct: ClassType => ct.tcd.cd.isGlobal
    case _ => false
  }

}
