/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.transformers.{TransformerOp, TransformerWithExprOp}

trait SymbolOps extends ast.SymbolOps { self: TypeOps =>
  import trees._
  import symbols._

  override protected def createTransformer[P <: PathLike[P]](
    path: P, f: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr
  )(implicit pp: PathProvider[P]): TransformerWithPC[P] = {
    new TransformerWithPC[P](path, f) with imperative.TransformerWithPC with TransformerWithExprOp
  }
}

