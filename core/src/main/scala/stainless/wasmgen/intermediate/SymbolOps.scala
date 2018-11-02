/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package wasmgen
package intermediate

trait SymbolOps extends ast.SymbolOps { self: TypeOps =>
  import trees._

  override def isImpureExpr(expr: Expr): Boolean = expr match {
    case Record(_, _) | RecordSelector(_, _) | FunctionPointer(_)
       | CastUp(_, _) | Sequence(_) | NewArray(_, _) => false
    case CastDown(_, _) | Output(_) | ArraySet(_, _, _) => true
    case other => super.isImpureExpr(other)
  }

}
