/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import inox.ast.Identifier

trait Expressions extends stainless.ast.Expressions { self: Trees =>

  /** Represents a value of a record type at runtime.
    * Has to be passed arguments for all fields,
    * including those defined in ``tpe``s ancestors.
    */
  sealed case class Record(tpe: RecordType, fields: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      checkParamTypes(fields, tpe.getRecord.allFields, tpe)
    }
  }

  /** Select a field of a record by name */
  sealed case class RecordSelector(record: Expr, selector: Identifier) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols) = {
      record.getType match {
        case RecordType(id) =>
          s.getRecord(id).allFields
            .find(_.id == selector)
            .map(_.tpe).getOrElse(Untyped)
        case _ =>
          Untyped
      }
    }
  }

  /** Represents a function pointer. It is the only runtime value that can have a function type */
  sealed case class FunctionPointer(id: Identifier) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      s.lookupFunction(id)
        .map(tfd => FunctionType(tfd.params.map(_.getType), tfd.getType))
        .getOrElse(Untyped)
    }
  }

  /** Cast an expression to a type lower in the type hierarchy.
    * If the runtime value does not conform to the cast type,
    * the program will fail.
    */
  sealed case class CastDown(e: Expr, subtype: RecordType) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      e.getType match {
        case supertype: RecordType if subtype conformsWith supertype => subtype
        case _ => Untyped
      }
    }
  }

  /** Cast an expression to a type higher in its type hierarchy.
    * This will never fail at runtime (if it is well-typed).
    */
  sealed case class CastUp(e: Expr, supertype: RecordType) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = e.getType match {
      case subtype: RecordType if subtype conformsWith supertype => supertype
      case _ => Untyped
    }
  }

  /** Print a message to the output */
  sealed case class Output(msg: Expr) extends Expr {
    def getType(implicit s: Symbols) = {
      msg.getType match {
        case StringType() => UnitType()
        case _ => Untyped
      }
    }
  }

  /** Execute all expressions in 'es' one after the other. All but the last have to be of UnitType.
    * If you are not sure that the requirement holds use [[Constructors.sequence]]
    */
  sealed case class Sequence(es: Seq[Expr]) extends Expr {
    require(es.size >= 2)
    def getType(implicit s: Symbols) = {
      checkParamTypes(es.init, List.fill(es.size - 1)(UnitType()), es.last.getType)
    }
  }

  sealed case class NewArray(length: Expr, init: Option[Expr]) extends Expr {
    def getType(implicit s: Symbols) =
      checkParamTypes(
        Seq(length) ++ init.toSeq,
        Seq(Int32Type()) ++ init.toSeq.map(_ => AnyRefType),
        ArrayType(AnyRefType)
      )
  }

  sealed case class ArraySet(array: Expr, index: Expr, value: Expr) extends Expr {
    def getType(implicit s: Symbols) = (array.getType, index.getType, value.getType) match {
      case (ArrayType(base1), Int32Type(), base2) if base1 == base2 => UnitType()
      case _ => Untyped
    }
  }

}
