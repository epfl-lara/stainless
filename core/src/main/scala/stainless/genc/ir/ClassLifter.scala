/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import IRs.{ NIR, LIR }

import collection.mutable.{ Map => MutableMap, Set => MutableSet }

// Lift class types to their hierarchy top type in order to properly use tagged union.
final class ClassLifter(val ctx: inox.Context) extends Transformer(NIR, LIR) {
  import from._

  type Env = Boolean // === lift flag
  val Ø = false

  private val lift = true

  // We use a global database to ease the recursion. This works because ValDef's are unique.
  private val valDB = MutableMap[ValDef, (to.ValDef, to.ClassType)]() // known runtime class type for values
  private val arrayDB = MutableMap[ValDef, (to.ValDef, to.ClassType)]() // idem but for array elements

  private val fieldValDB = MutableMap[(to.ClassDef, Id), to.ClassType]() // idem for class field type
  private val fieldArrayDB = MutableMap[(to.ClassDef, Id), to.ClassType]() // idem for the elements of class fields that are arrays

  private def isKnownValField(cd: to.ClassDef, fieldId: to.Id): Boolean = fieldValDB contains (cd -> fieldId)
  private def isKnownArrayField(cd: to.ClassDef, fieldId: to.Id): Boolean = fieldArrayDB contains (cd -> fieldId)

  // Lift context, params & return type
  override def recImpl(fd: FunDef)(using Env): to.FunDef = {
    val id = fd.id

    val returnType = rec(fd.returnType)(using lift)
    val ctx = fd.ctx map lift
    val params = fd.params map lift

    // Handle recursive functions
    val newer = to.FunDef(id, returnType, ctx, params, null, fd.isExported, fd.isPure)
    registerFunction(fd, newer)

    newer.body = rec(fd.body)(using lift)

    newer
  }

  // Lift fields types
  override def recImpl(cd0: ClassDef, parent: Option[to.ClassDef])(using Env): to.ClassDef = {
    val id = cd0.id
    val isAbstract = cd0.isAbstract

    val valFieldsToRegister = MutableSet[(Id, to.ClassType)]()
    val arrayFieldsToRegister = MutableSet[(Id, to.ClassType)]() // for the element of the arrays

    val fields = cd0.fields map { vd0 => // This is similar to lift(ValDef) but here we need to defer the registration
      val vd = rec(vd0)(using lift)

      // "Pre"-register fields if class type or array type was lifted
      val typ = rec(vd0.getType)(using !lift)
      typ match {
        case ct @ to.ClassType(c) if c.hierarchyTop != c =>
          valFieldsToRegister += (vd.id -> ct)

        case to.ArrayType(ct @ to.ClassType(c), _) if c.hierarchyTop != c =>
          arrayFieldsToRegister += (vd.id -> ct)

        case _ => ()
      }

      vd
    }

    val cd = to.ClassDef(id, parent, fields, isAbstract, cd0.isExported, cd0.isPacked)

    // Actually register the classes/arrays now that we have the corresponding ClassDef
    valFieldsToRegister foreach { case (id, ct) =>
      fieldValDB += (cd, id) -> ct
    }

    arrayFieldsToRegister foreach { case (id, ct) =>
      fieldArrayDB += (cd, id) -> ct
    }

    cd
  }

  override def recImpl(e: Expr)(using env: Env): (to.Expr, Env) = e match {
    case Decl(vd0, optInit0) =>
      val vd = lift(vd0)
      val optInit = optInit0.map(init => rec(init)(using lift))
      to.Decl(vd, optInit) -> env

    case FieldAccess(Castable(asa), fieldId) =>
      to.FieldAccess(asa, fieldId) -> env

    case App(fun0, ctx0, args0) =>
      val fun = recCallable(fun0)

      // Don't pass a casted object but the object itself
      // (this can happen with pattern matching translation).
      val ctx = ctx0 map removeTopCast
      val args = args0 map removeTopCast

      to.App(fun, ctx, args) -> env

    case _ => super.recImpl(e)
  }

  override def rec(typ: Type)(using lift: Env): to.Type = typ match {
    case ClassType(clazz) if lift => to.ClassType(rec(clazz.hierarchyTop))
    case ArrayType(ArrayType(ClassType(_), _), _) =>
      ctx.reporter.fatalError("Multidimentional arrays of objects are not yet supported")
    case typ => super.rec(typ)
  }

  private def removeTopCast(e: Expr): to.Expr = rec(e)(using lift) match {
    case to.AsA(expr, _) => expr
    case e => e
  }

  private object Castable {
    def unapply(e: Expr): Option[to.Expr] = e match {
      case CastableImpl(asa, _) => Some(asa)
      case _ => None
    }
  }

  private object ClassTypedExpr {
    def unapply(e: Expr): Option[(to.Expr, to.ClassDef)] = e.getType match {
      case ClassType(cd) => Some(rec(e)(using lift) -> rec(cd)(using !lift))
      case _ => None
    }
  }

  // An expression can be safely cast to it known initial type (i.e. before lifting) when:
  //  - the vd referenced by a binding was registered with its unlifted type;
  //  - accessing a class field that was lifted, either by recursion or through an expression
  //    (e.g. function call) of a known conrete class type (before lifting);
  //  - accessing an element of an array that was lifted through a registered vd or a field
  //    access.
  private object CastableImpl {
    def unapply(e0: Expr): Option[(to.AsA, to.ClassDef)] = e0 match {
      case Binding(vd0) if valDB contains vd0 =>
        val (vd, ct) = valDB(vd0)
        val asa = to.AsA(to.Binding(vd), ct)
        val cd = ct.clazz

        Some(asa -> cd)

      case FieldAccess(CastableImpl(asa1, cd1), fieldId) if isKnownValField(cd1, fieldId) =>
        val ct2 = fieldValDB(cd1 -> fieldId)
        val asa2 = to.AsA(to.FieldAccess(asa1, fieldId), ct2)
        val cd2 = ct2.clazz

        Some(asa2 -> cd2)

      case FieldAccess(ClassTypedExpr(e, cd1), fieldId) if isKnownValField(cd1, fieldId) =>
        val ct2 = fieldValDB(cd1 -> fieldId)
        val asa2 = to.AsA(to.FieldAccess(e, fieldId), ct2)
        val cd2 = ct2.clazz

        Some(asa2 -> cd2)

      case ArrayAccess(Binding(vd0), index0) if arrayDB contains vd0 =>
        val (vd, ct) = arrayDB(vd0)
        val asa = to.AsA(to.ArrayAccess(to.Binding(vd), rec(index0)(using lift)), ct)
        val cd = ct.clazz

        Some(asa -> cd)

      case ArrayAccess(FieldAccess(CastableImpl(asa1, cd1), fieldId), index0) if isKnownArrayField(cd1, fieldId) =>
        val ct2 = fieldArrayDB(cd1 -> fieldId)
        val asa2 = to.AsA(to.ArrayAccess(to.FieldAccess(asa1, fieldId), rec(index0)(using lift)), ct2)
        val cd2 = ct2.clazz

        Some(asa2 -> cd2)

      case ArrayAccess(FieldAccess(ClassTypedExpr(e, cd1), fieldId), index0) if isKnownArrayField(cd1, fieldId) =>
        val ct2 = fieldArrayDB(cd1 -> fieldId)
        val asa2 = to.AsA(to.ArrayAccess(to.FieldAccess(e, fieldId), rec(index0)(using lift)), ct2)
        val cd2 = ct2.clazz

        Some(asa2 -> cd2)

      case _ =>
        None
    }
  }

  private def lift(vd0: ValDef): to.ValDef = {
    val vd = rec(vd0)(using lift)
    val typ = rec(vd0.getType)(using !lift)

    // Register val if class type or array type was lifted
    typ match {
      case ct @ to.ClassType(c) if c.hierarchyTop != c =>
        valDB += vd0 -> (vd, ct)

      case to.ArrayType(ct @ to.ClassType(c), _) if c.hierarchyTop != c =>
        arrayDB += vd0 -> (vd, ct)

      case _ => ()
    }

    vd
  }

}
