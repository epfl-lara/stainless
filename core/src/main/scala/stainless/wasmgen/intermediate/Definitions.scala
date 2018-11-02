/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import stainless.{FreshIdentifier, Identifier}

trait Definitions extends stainless.ast.Definitions { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols { self0: Symbols =>
    val records: Map[Identifier, RecordSort]
    val sorts: Map[Identifier, ADTSort] = Map()

    def lookupRecord(id: Identifier): Option[RecordSort] = records.get(id)
    def getRecord(id: Identifier): RecordSort = records.getOrElse(id, throw ADTLookupException(id))
  }

  /** Tags dynamically called functions */
  case object Dynamic extends Flag("dynamic", Seq.empty)

  /** A record sort represents a sequence of named fields.
    * A record sort may extend another record sort.
    * A record contains all the parent's fields in order,
    * followed by its own defined fields.
    */
  class RecordSort(
    val id: Identifier,
    val parent: Option[Identifier],
    val fields: Seq[ValDef],
    val flags: Seq[Flag] = Seq()
  ) extends Definition {

    def lookupParent(implicit s: Symbols): Option[RecordSort] = {
      parent.map(s.getRecord)
    }
    def allFields(implicit s: Symbols): Seq[ValDef] = {
      lookupParent.toSeq.flatMap(_.allFields) ++ fields
    }
    def ancestors(implicit s: Symbols): Seq[Identifier] = {
      id +: lookupParent.toSeq.flatMap(_.ancestors)
    }
    def conformsWith(ancestor: Identifier)(implicit s: Symbols): Boolean = ancestors.contains(ancestor)
  }

  private[wasmgen] val typeTagID = FreshIdentifier("typeTag")
  private[wasmgen] val typeTag = ValDef(typeTagID, Int32Type())
  private[wasmgen] val funPointerId = FreshIdentifier("fPointer")
  private[wasmgen] val boxedValueId = FreshIdentifier("value")

  /** Represents the top of the record hierarchy. It is the only record sort without a parent.
    * Defines only one field, which represents the type-tag of the runtime value.
    */
  object AnyRefSort extends RecordSort(FreshIdentifier("anyref"), None, Seq(typeTag), Seq())

  private def prependParamType(tpe: Type, ft: FunctionType) =
    FunctionType(tpe +: ft.from, ft.to)

  /** A record which defines a single field of a function type (function pointer).
    * It is used as a base of all closures for this function type.
    */
  sealed class FunPointerSort(id: Identifier, ft: FunctionType)
    extends RecordSort(
      id,
      Some(AnyRefSort.id),
      Seq(ValDef(funPointerId, prependParamType(RecordType(id), ft))))

  /** Represents a closure, containing a function pointer plus the closure's environment
    */
  sealed class ClosureSort(parent: Identifier, env: Seq[ValDef])
    extends RecordSort(FreshIdentifier("closure"), Some(parent), env)

  /** Represents a record sort corresponding to an ADT of a high-level language.
    * This sort will never be instantiated at runtime.
    */
  sealed class RecordADTSort(id: Identifier)
    extends RecordSort(id, Some(AnyRefSort.id), Seq())

  /** Represents a record sort corresponding to an ADT constructor of a high-level language.
    * Defines a unique type tag which differentiates values of this constructor at runtime.
    */
  sealed class ConstructorSort(
    id: Identifier,
    parent: Identifier,
    val typeTag: Int,
    fields: Seq[ValDef]
  ) extends RecordSort(id, Some(parent), fields)

  /** Represents a box containing a value of an elementary (or array) type.
    * Useful to implement boxing for high-level languages with parametric polymorphism.
    */
  sealed class BoxedSort(tpe: Type)
    extends RecordSort(
      FreshIdentifier("Boxed" + tpe.asString(PrinterOptions())),
      Some(AnyRefSort.id),
      Seq(ValDef(boxedValueId, tpe)))

  def typeToTag(tpe: Type): Int = tpe match {
    case BooleanType() => 0
    case CharType() => 1
    case BVType(_, 32) => 2
    case BVType(_, 64) => 3
    case IntegerType() => 4
    case RealType() => 5
    case ArrayType(AnyRefType) => 6
    case StringType() => 7
    case FunctionType(_, _) => 8
  }

  val lastReservedTag: Int = typeToTag(FunctionType(Seq(), Untyped))

}
