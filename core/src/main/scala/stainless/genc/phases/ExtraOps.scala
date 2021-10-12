/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import extraction.throwing.trees._

import collection.mutable.{ Set => MutableSet }

private[genc] object ExtraOps {
  // copied from AdtSpecialization
  def root(id: Identifier)(implicit symbols: Symbols): Identifier = {
    symbols.getClass(id).parents.map(ct => root(ct.id)).headOption.getOrElse(id)
  }

  case class ManualDef(code: String, includes: Seq[String])

  private val manualDefAnnotation = "cCode.function"

  implicit class FunAbsOps(val fa: FunAbstraction)  {
    def isManuallyDefined = hasAnnotation(manualDefAnnotation)
    def isExtern = fa.flags contains Extern
    def isDropped = hasAnnotation("cCode.drop") || fa.flags.contains(Ghost)
    def isVal: Boolean = fa.isInstanceOf[Outer] && fa.asInstanceOf[Outer].fd.isVal

    def extAnnotations: Map[String, Seq[Any]] = fa.flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap
    def annotations: Set[String] = extAnnotations.keySet

    def getManualDefinition = {
      assert(isManuallyDefined)

      val Seq(StringLiteral(code), StringLiteral(includes0)) = fa.extAnnotations(manualDefAnnotation)

      val includes =
        if (includes0.isEmpty) Nil
        else { includes0 split ':' }.toSeq

      ManualDef(code.stripMargin, includes)
    }

    private def hasAnnotation(annot: String) = annotations contains annot
  }

  // Extra tools on FunDef, especially for annotations
  implicit class FunDefOps(val fd: FunDef) {
    def isMain = fd.id.name == "main"

    def isExtern          = fd.flags contains Extern
    def isDropped         = hasAnnotation("cCode.drop") || fd.flags.contains(Ghost)
    def isExported        = hasAnnotation("cCode.export")
    def isManuallyDefined = hasAnnotation(manualDefAnnotation)
    def isVal             =
      (fd.flags.exists(_.name == "accessor") || fd.flags.exists { case IsField(_) => true case _ => false }) &&
      fd.tparams.isEmpty && fd.params.isEmpty

    def extAnnotations: Map[String, Seq[Any]] = fd.flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap
    def annotations: Set[String] = extAnnotations.keySet

    def getManualDefinition = {
      assert(isManuallyDefined)

      val Seq(StringLiteral(code), StringLiteral(includes0)) = fd.extAnnotations(manualDefAnnotation)

      val includes =
        if (includes0.isEmpty) Nil
        else { includes0 split ':' }.toSeq

      ManualDef(code.stripMargin, includes)
    }

    def isGeneric = fd.tparams.length > 0

    def hasAnnotation(annot: String) = annotations contains annot
  }

  // Extra tools on ClassDef, especially for annotations, inheritance & generics
  implicit class ClassDefOps(val cd: ClassDef) {
    def isManuallyTyped = hasAnnotation(manualTypeAnnotation)
    def isDropped       = hasAnnotation(droppedAnnotation)
    def isExported      = hasAnnotation("cCode.export")
    def isPacked        = hasAnnotation("cCode.pack")
    def isGlobal        = cd.flags.exists(_.name.startsWith("cCode.global"))
    def isGlobalDefault = cd.flags.exists(_.name == "cCode.global")
    def isGlobalUninitialized = cd.flags.exists(_.name == "cCode.globalUninitialized")
    def isGlobalExternal = cd.flags.exists(_.name == "cCode.globalExternal")

    def extAnnotations: Map[String, Seq[Any]] = cd.flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap
    def annotations: Set[String] = extAnnotations.keySet

    def getManualType = {
      assert(isManuallyTyped)

      val Seq(StringLiteral(alias), StringLiteral(includes0)) = cd.extAnnotations(manualTypeAnnotation)
      val include = if (includes0.isEmpty) None else Some(includes0)

      ManualType(alias, include)
    }

    case class ManualType(alias: String, include: Option[String])

    def isCandidateForInheritance = cd.isAbstract || !cd.parents.isEmpty

    def isGeneric = cd.tparams.length > 0

    def isRecursive(implicit sym: Symbols): Boolean = {
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
    def isCandidate(implicit symbols: Symbols): Boolean = {
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
    def isCaseObject(implicit symbols: Symbols): Boolean = {
      val id = cd.id
      isCandidate && (symbols.getClass(id).flags contains IsCaseObject)
    }

    // Check whether the class has some fields or not
    def isEmpty = cd.fields.isEmpty

    def hasAnnotation(annot: String) = cd.annotations contains annot
    private val manualTypeAnnotation = "cCode.typedef"
    private val droppedAnnotation = "cCode.drop"
  }

  def isGlobal(tpe: Type)(implicit symbols: Symbols): Boolean = tpe match {
    case ct: ClassType => ct.tcd.cd.isGlobal
    case _ => false
  }

}
