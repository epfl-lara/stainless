/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, ListBuffer}

trait StructuralSize { self: SolverProvider =>
  val checker: ProcessingPipeline

  import checker.program.trees._
  import checker.program.symbols.{given, _}
  import dsl._

  val sizes: SizeFunctions { val trees: checker.program.trees.type }

  def functions: Seq[FunDef] = sizes.getFunctions(checker.program.symbols).toSeq

  class TransformerImpl(override val s: checker.program.trees.type, override val t: checker.program.trees.type)
    extends inox.transformers.SymbolTransformer {
    def transform(s: Symbols): Symbols = {
      s.withFunctions(functions.toSeq)
    }
  }
  registerTransformer(new TransformerImpl(checker.program.trees, checker.program.trees))

  def integerAbs: FunDef = sizes.integerAbs

  def bvAbs(tpe: BVType): FunDef = sizes.bvAbs(tpe)

  def bvAbs2Integer(tpe: BVType): FunDef = sizes.bvAbs2Integer(tpe)

  def fullSize(expr: Expr): Expr = sizes.fullSize(expr)

  // An ADT sort corresponds to a container type if (and only if) it has
  // a single non-recursive constructor
  object ContainerType {
    def unapply(c: ADTType): Option[Seq[ValDef]] = c.getSort.constructors match {
      case Seq(tcons) =>
        if (tcons.fields.exists(vd => isSubtypeOf(vd.tpe, c))) None
        else Some(tcons.fields)
      case _ => None
    }
  }

  def flatTypesPowerset(tpe: Type): Set[Expr => Expr] = {
    def powerSetToFunSet(l: IterableOnce[Expr => Expr]): Set[Expr => Expr] = {
      l.iterator.to(Set).subsets().filter(_.nonEmpty).map{
        (reconss: Set[Expr => Expr]) => (e : Expr) =>
          tupleWrap(reconss.toSeq map { f => f(e) })
      }.toSet
    }

    powerSetToFunSet(flatTypes(tpe))
  }

  def flatTypes(tpe: Type): Set[Expr => Expr] = {
    def rec(tpe: Type): Set[Expr => Expr] = tpe match {
      case ContainerType(fields) =>
        fields.flatMap {
          vd => rec(vd.tpe).map(recons => (e: Expr) => recons(adtSelector(e, vd.id)))
        }.toSet
      case TupleType(tpes) =>
        tpes.indices.flatMap {
          index => rec(tpes(index)).map(recons => (e: Expr) => recons(tupleSelect(e, index + 1, true)))
        }.toSet
      case _ => Set((e: Expr) => e)
    }

    rec(tpe)
  }

  def lexicographicallySmaller(s1: Seq[Expr], s2: Seq[Expr], strict: Boolean, sizeOfOneExpr: Expr => Expr): Expr = {
    // Note: The Equal and LessThan ASTs work for both BigInt and Bitvector

    val sameSizeExprs = for ((arg1, arg2) <- s1 zip s2) yield Equals(sizeOfOneExpr(arg1), sizeOfOneExpr(arg2))

    val lessBecauseLessAtFirstDifferentPos = {
      orJoin(
        for (firstDifferent <- 0 until scala.math.min(s1.length, s2.length)) yield {
          val firstPartEqual = andJoin(sameSizeExprs.take(firstDifferent))
          val lastDifferent  = LessThan(sizeOfOneExpr(s1(firstDifferent)), sizeOfOneExpr(s2(firstDifferent)))
          and(firstPartEqual, lastDifferent)
        }
      )
    }

    // Strict case applies when the first tuple is longer.
    if(strict || s1.length > s2.length) {
      lessBecauseLessAtFirstDifferentPos
    } else {
      or(andJoin(sameSizeExprs), lessBecauseLessAtFirstDifferentPos)
    }
  }
}
