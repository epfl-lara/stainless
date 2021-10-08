/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

import inox.transformers.{TransformerOp, TransformerWithExprOp, TransformerWithTypeOp}

trait SymbolOps extends TypeOps with ast.SymbolOps { self =>
  import trees._
  import symbols.{given, _}

  override protected def transformerWithPC[P <: PathLike[P]](
    path: P,
    theExprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    theTypeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(using PathProvider[P]): StainlessTransformerWithPC[P] = {
    class Impl(override val s: self.trees.type,
               override val t: self.trees.type,
               override val symbols: self.symbols.type)
              (using override val pp: PathProvider[P])
      extends StainlessTransformerWithPC[P](s, t, symbols)
        with innerfuns.TransformerWithPC
        with TransformerWithExprOp
        with TransformerWithTypeOp {
      override protected def exprOp(expr: s.Expr, env: Env, op: TransformerOp[s.Expr, Env, t.Expr]): t.Expr = {
        theExprOp(expr, env, op)
      }

      override protected def typeOp(ty: s.Type, env: Env, op: TransformerOp[s.Type, Env, t.Type]): t.Type = {
        theTypeOp(ty, env, op)
      }
    }

    new Impl(self.trees, self.trees, self.symbols)
  }
}
