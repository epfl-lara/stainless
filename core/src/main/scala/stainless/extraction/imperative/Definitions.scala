/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait Definitions extends oo.Trees { self: Trees =>
  override type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols with SymbolOps with TypeOps {
    self0: Symbols =>

    override protected def ensureWellFormedFunction(fd: FunDef): Unit = {
      exprOps.preTraversal {
        case fa @ self.FieldAssignment(obj, field, _) =>
          // if the field that is assigned is not '@var', throw
          if (fa.getField(self0).exists(fieldVd => !fieldVd.flags.contains(IsVar))) {
            throw NotWellFormedException(
              fd,
              Some(s"cannot assign to immutable field '${field.name}' of class '${obj.getType}'")
            )
          }
        case _ => ()
      }(fd.fullBody)

      super.ensureWellFormedFunction(fd)
    }
  }
}
