/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

import inox.transformers.{TransformerOp, TransformerWithExprOp, TransformerWithTypeOp}

trait SymbolOps extends ast.SymbolOps { self: TypeOps =>
  import trees._
  import symbols._

  override protected def transformerWithPC[P <: PathLike[P]](
    path: P,
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(implicit pp: PathProvider[P]): TransformerWithPC[P] = {
    new TransformerWithPC[P](path, exprOp, typeOp)
      with innerfuns.TransformerWithPC
      with TransformerWithExprOp
      with TransformerWithTypeOp
  }
}
