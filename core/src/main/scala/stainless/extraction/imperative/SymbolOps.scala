/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait SymbolOps extends stainless.ast.SymbolOps { self: TypeOps =>
  import trees._
  import symbols._

  override protected def createTransformer[P <: PathLike[P]](path: P, f: (Expr, P, TransformerOp[P]) => Expr)
                                                            (implicit ppP: PathProvider[P]): TransformerWithPC[P] =
    new super.TransformerWithPC[P](path, f) with imperative.TransformerWithPC with super.TransformerWithFun {
      override val pp = ppP
    }
}

