/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

import scala.quoted._

import inox.utils._

/**
  * Macro for creating Serializer for Stainless AST.
  *
  * Due to technical limitations, the return type is approximated with a general type projection
  * as opposed to being a path-dependent type over `stainlessSerializer`.
  */
inline def stainlessClassSerializerMacro[T](inline stainlessSerializer: StainlessSerializer, inline id: Int): InoxSerializer#Serializer[T] =
  ${ stainlessClassSerializerMacroImpl[T]('stainlessSerializer, 'id) }

// This dummy function delegates the actual work to `classSerializerMacroWorkhorse`
def stainlessClassSerializerMacroImpl[T](stainlessSerializer: Expr[StainlessSerializer], id: Expr[Int])
                                        (using q: Quotes, t: Type[T]): Expr[InoxSerializer#Serializer[T]] = {
  import quotes.reflect._
  // Prefixes we would like to substitute by `StainlessSerializer.this.trees`
  // For instance, if we see the type `inox.ast.Expressions.Assume`,
  // we replace it with `StainlessSerializer.this.trees.Assume`.
  // (see docstring of classSerializerMacroWorkhorse for an actual example)
  val prefixesToSubst = Set(
    This(TypeTree.of[inox.ast.Trees].tpe.typeSymbol).tpe,
    This(TypeTree.of[inox.ast.Expressions].tpe.typeSymbol).tpe,
    This(TypeTree.of[inox.ast.Types].tpe.typeSymbol).tpe,
    This(TypeTree.of[inox.ast.Definitions].tpe.typeSymbol).tpe,

    This(TypeTree.of[stainless.ast.Trees].tpe.typeSymbol).tpe,
    This(TypeTree.of[stainless.ast.Expressions].tpe.typeSymbol).tpe,
    This(TypeTree.of[stainless.ast.Types].tpe.typeSymbol).tpe,
    This(TypeTree.of[stainless.ast.Definitions].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.termination.Trees].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.trace.Trees].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.inlining.Trees].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.innerfuns.Trees].tpe.typeSymbol).tpe,
    This(TypeTree.of[extraction.innerfuns.Definitions].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.oo.Trees].tpe.typeSymbol).tpe,
    This(TypeTree.of[extraction.oo.Definitions].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.imperative.Trees].tpe.typeSymbol).tpe,
    This(TypeTree.of[extraction.imperative.Definitions].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.throwing.Trees].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.methods.Trees].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.innerclasses.Trees].tpe.typeSymbol).tpe,
    This(TypeTree.of[extraction.innerclasses.Types].tpe.typeSymbol).tpe,
    This(TypeTree.of[extraction.innerclasses.Definitions].tpe.typeSymbol).tpe,

    This(TypeTree.of[extraction.xlang.Trees].tpe.typeSymbol).tpe
  )

  inox.utils.classSerializerMacroWorkhorse(stainlessSerializer, id)(using q, t)(prefixesToSubst)
}
