/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait Definitions extends oo.Trees { self: Trees =>
  override type Symbols >: Null <: ImperativeAbstractSymbols

  trait ImperativeAbstractSymbols
    extends OOAbstractSymbols
       with imperative.SymbolOps
       with imperative.TypeOps {
    self0: Symbols =>

    // The only value that can be assigned to `trees`, but that has to be
    // done in a concrete class explicitly overriding `trees`
    // Otherwise, we can run into initialization issue.
    protected val trees: self.type
    // More or less the same here
    protected val symbols: this.type

    override protected def ensureWellFormedFunction(fd: FunDef): Unit = {
      exprOps.preTraversal {
        case fa @ self.FieldAssignment(obj, field, _) =>
          // if the field that is assigned is not '@var', throw
          if (fa.getField(using self0).exists(fieldVd => !fieldVd.flags.contains(IsVar))) {
            throw NotWellFormedException(
              fd,
              Some(s"cannot assign to immutable field '${field.name}' of class '${obj.getType(using self0)}'")
            )
          }
        case _ => ()
      }(fd.fullBody)

      super.ensureWellFormedFunction(fd)
    }
  }
}
