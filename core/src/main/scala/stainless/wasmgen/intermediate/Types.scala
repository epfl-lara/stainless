/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.intermediate

import inox.ast.Identifier

trait Types extends inox.ast.Types { self: Trees =>
  /** A record type identified by the Identifier given as argument */
  sealed case class RecordType(record: Identifier) extends Type {
    def lookupRecord(implicit s: Symbols): Option[RecordSort] = s.lookupRecord(record)

    def getRecord(implicit s: Symbols): RecordSort = s.getRecord(record)
  
    def parent(implicit s: Symbols): Option[RecordType] = {
      s.getRecord(record).parent.map(RecordType)
    }

    def conformsWith(superType: Type)(implicit s: Symbols): Boolean = superType match {
      case RecordType(record2) =>
        getRecord.ancestors contains record2
      case _ => false
    }
  }

  /** The top of the record type hierarchy, corresponding to
    *  [[trees.AnyRefSort]]
    */
  val AnyRefType = RecordType(AnyRefSort.id)

}
