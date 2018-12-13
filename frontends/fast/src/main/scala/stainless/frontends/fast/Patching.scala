package stainless.frontends.fast

import scala.collection.mutable
import stainless.extraction.xlang.{trees => xt}
import stainless.frontends.fast.Patching.trees

object Patching extends IRs{

  val trees = xt

  val idToClassMap: scala.collection.mutable.Map[inox.Identifier, trees.ClassType] = new mutable.HashMap()

  def patchGuard(optGuard: Option[xt.Expr]): Option[xt.Expr] = optGuard match {
    case Some(expr) => Some(patchExpr(expr))
    case None => None
  }

  def patchOptionalBinder(binder: Option[xt.ValDef]): Option[trees.ValDef] = binder match {
    case Some(bind) => Some(patchDef(bind).asInstanceOf[trees.ValDef])
    case None => None
  }

  def patchPattern(pattern: xt.Pattern): xt.Pattern = pattern match {
    case trees.LiteralPattern(binder, lit) =>
      trees.LiteralPattern(patchOptionalBinder(binder), patchExpr(lit).asInstanceOf[trees.Literal[Any]])
    case trees.TuplePattern(binder, subPatterns) =>
      trees.TuplePattern(patchOptionalBinder(binder), subPatterns.map(patchPattern))
    case trees.WildcardPattern(binder) =>
      trees.WildcardPattern(patchOptionalBinder(binder))
    case trees.InstanceOfPattern(binder, tpe) =>
      trees.InstanceOfPattern(patchOptionalBinder(binder), patchType(tpe))
  }

  def patchMatchCase(matchCase: xt.MatchCase): xt.MatchCase =
    xt.MatchCase(patchPattern(matchCase.pattern), patchGuard(matchCase.optGuard), patchExpr(matchCase.rhs))

  def patchExpr(expr: trees.Expr): trees.Expr = expr match {
    // patched expressions
    case trees.Variable(ident, tpe, flags) => new trees.Variable(ident, patchType(tpe), flags)
    case trees.ADT(ident, tps, args) =>
      trees.ClassConstructor(trees.ClassType(ident, tps), args.map(patchExpr))
    case trees.IsConstructor(expr, id) =>
      trees.IsInstanceOf(patchExpr(expr), idToClassMap.getOrElse(id, trees.Untyped))
    case trees.ADTSelector(adt, selector) =>
      trees.ClassSelector(patchExpr(adt), selector)
    // mapped expression
    case trees.Assume(pred, body) => trees.Assume(patchExpr(pred), patchExpr(body))
    case trees.Let(valDef, value, body) =>
      trees.Let(patchDef(valDef).asInstanceOf[trees.ValDef],
        patchExpr(value), patchExpr(body))
    case trees.Application(callee, args) =>
      trees.Application(patchExpr(callee), args.map(patchExpr))
    case trees.Lambda(params, body) =>
      trees.Lambda(patchParams(params), patchExpr(body))
    case trees.Forall(params, body) =>
      trees.Forall(patchParams(params), patchExpr(body))
    case trees.Choose(valDef, pred) =>
      trees.Choose(patchDef(valDef).asInstanceOf[trees.ValDef], patchExpr(pred))
    case trees.FunctionInvocation(id, tps, args) =>
      trees.FunctionInvocation(id, tps.map(patchType), args.map(patchExpr))
    case trees.IfExpr(cond, thenBranch, elseBranch) =>
      trees.IfExpr(patchExpr(cond), patchExpr(thenBranch), patchExpr(elseBranch))
    case trees.Equals(left, right) =>
      trees.Equals(patchExpr(left), patchExpr(right))
    case trees.Or(exprs) => trees.Or(exprs.map(patchExpr))
    case trees.Implies(left, right) => trees.Implies(patchExpr(left), patchExpr(right))
    case trees.Not(expr) => trees.Not(patchExpr(expr))
    case trees.StringConcat(left, right) =>
      trees.StringConcat(patchExpr(left), patchExpr(right))
    case trees.SubString(left, start, end) =>
      trees.SubString(patchExpr(left), patchExpr(start), patchExpr(end))
    case trees.StringLength(expr) => trees.StringLength(patchExpr(expr))
    case trees.Plus(lhs, rhs) => trees.Plus(patchExpr(lhs), patchExpr(rhs))
    case trees.Minus(lhs, rhs) => trees.Minus(patchExpr(lhs), patchExpr(rhs))
    case trees.UMinus(expr) => trees.UMinus(patchExpr(expr))
    case trees.Times(lhs, rhs) => trees.Times(patchExpr(lhs), patchExpr(rhs))
    case trees.Division(lhs, rhs) =>
      trees.Division(patchExpr(lhs), patchExpr(rhs))
    case trees.Remainder(lhs, rhs) =>
      trees.Remainder(patchExpr(lhs), patchExpr(rhs))
    case trees.Modulo(lhs, rhs) =>
      trees.Modulo(patchExpr(lhs), patchExpr(rhs))
    case trees.LessThan(lhs, rhs) =>
      trees.LessThan(patchExpr(lhs), patchExpr(rhs))
    case trees.GreaterThan(lhs, rhs) =>
      trees.GreaterThan(patchExpr(lhs), patchExpr(rhs))
    case trees.LessEquals(lhs, rhs) =>
      trees.LessEquals(patchExpr(lhs), patchExpr(rhs))
    case trees.GreaterEquals(lhs, rhs) =>
      trees.GreaterEquals(patchExpr(lhs), patchExpr(rhs))
    case trees.BVNot(expr) =>
      trees.BVNot(patchExpr(expr))
    case trees.BVAnd(lhs, rhs) =>
      trees.BVAnd(patchExpr(lhs), patchExpr(rhs))
    case trees.BVOr(lhs, rhs) =>
      trees.BVOr(patchExpr(lhs), patchExpr(rhs))
    case trees.BVXor(lhs, rhs) =>
      trees.BVXor(patchExpr(lhs), patchExpr(rhs))
    case trees.BVShiftLeft(lhs, rhs)=>
      trees.BVShiftLeft(patchExpr(lhs), patchExpr(rhs))
    case trees.BVAShiftRight(lhs, rhs) =>
      trees.BVAShiftRight(patchExpr(lhs), patchExpr(rhs))
    case trees.BVLShiftRight(lhs, rhs) =>
      trees.BVLShiftRight(lhs, rhs)
    case trees.BVNarrowingCast(expr, newType) =>
      trees.BVNarrowingCast(patchExpr(expr), newType)
    case trees.BVWideningCast(expr, newType) =>
      trees.BVWideningCast(patchExpr(expr), newType)
    case trees.Tuple(exprs) =>
      trees.Tuple(exprs.map(patchExpr))
    case trees.TupleSelect(expr, index) =>
      trees.TupleSelect(patchExpr(expr), index)
    case trees.FiniteSet(elements, tpe) =>
      trees.FiniteSet(elements.map(patchExpr), patchType(tpe))
    case trees.SetAdd(set, elem) =>
      trees.SetAdd(patchExpr(set), patchExpr(elem))
    case trees.ElementOfSet(element, set) =>
      trees.ElementOfSet(patchExpr(element), patchExpr(set))
    case trees.SubsetOf(lhs, rhs) =>
      trees.SubsetOf(patchExpr(lhs), patchExpr(rhs))
    case trees.SetIntersection(lhs, rhs) =>
      trees.SetIntersection(patchExpr(lhs), patchExpr(rhs))
    case trees.SetUnion(lhs, rhs) =>
      trees.SetUnion(patchExpr(lhs), patchExpr(rhs))
    case trees.SetDifference(lhs, rhs) =>
      trees.SetDifference(patchExpr(lhs), patchExpr(rhs))
    case trees.FiniteBag(elements, base) =>
      trees.FiniteBag(
        elements.map{a => (patchExpr(a._1), patchExpr(a._2))},
        patchType(base))
    case trees.BagAdd(bag, elem) =>
      trees.BagAdd(patchExpr(bag), patchExpr(elem))
    case trees.MultiplicityInBag(bag, elem) =>
      trees.MultiplicityInBag(patchExpr(bag), patchExpr(elem))
    case trees.BagIntersection(lhs, rhs) =>
      trees.BagIntersection(patchExpr(lhs), patchExpr(rhs))
    case trees.BagUnion(lhs, rhs) =>
      trees.BagUnion(patchExpr(lhs), patchExpr(rhs))
    case trees.BagDifference(lhs, rhs) =>
      trees.BagDifference(patchExpr(lhs), patchExpr(rhs))
    case trees.FiniteMap(pairs, default, keyType, valueType) =>
      trees.FiniteMap(pairs.map(a => (patchExpr(a._1), patchExpr(a._2))),
        patchExpr(default), patchType(keyType), patchType(valueType))
    case trees.MapApply(map, key) =>
      trees.MapApply(patchExpr(map), patchExpr(key))
    case trees.MapUpdated(map, key, value) =>
      trees.MapUpdated(patchExpr(map), patchExpr(key), patchExpr(value))
    case trees.And(exprs) => trees.And(exprs.map(patchExpr))
    case a: trees.Literal[Any] => a
    case trees.MatchExpr(scrutinee, cases) => trees.MatchExpr(patchExpr(scrutinee), cases.map(patchMatchCase(_)))
    case _ =>
      throw new Exception("Should not reach this branch in expression patching")
  }

  def patchDef(definition: trees.Definition): trees.Definition = definition match {
    case valDef: trees.ValDef => new trees.ValDef(patchExpr(valDef.toVariable).asInstanceOf[trees.Variable])
  }

  def patchParams(params: Seq[trees.ValDef]): Seq[xt.ValDef] =
    params.map(a => new xt.ValDef(patchExpr(a.toVariable).asInstanceOf[trees.Variable]))

  def patchType(tpe: trees.Type): xt.Type = tpe match {
    case trees.ADTType(typeId, tps) => trees.ClassType(typeId, tps.map(patchType))
    case _ => tpe
  }

  def patchFunction(function: trees.FunDef): trees.FunDef =
    new trees.FunDef(function.id, function.tparams, patchParams(function.params), patchType(function.returnType),
      patchExpr(function.fullBody), function.flags)

  /**
    * Does patching after the elaboration is finished
    *
    * @param definitions
    * @return
    */
  def patchAST(definitions: Seq[trees.Definition]): (Seq[trees.FunDef], Seq[trees.ClassDef]) = {
    val adts: Seq[trees.ADTSort] = definitions.flatMap {
      case a: trees.ADTSort => Some(a)
      case _ => None
    }

    val functions: Seq[trees.FunDef] = definitions.flatMap {
      case a: trees.FunDef => Some(a)
      case _ => None
    }

    var classDefs = Seq.empty[trees.ClassDef]

    adts.foreach(adt => {
      classDefs = classDefs :+ new xt.ClassDef(adt.id.asInstanceOf[stainless.ast.SymbolIdentifier],
        adt.tparams.asInstanceOf[Seq[xt.TypeParameterDef]],
        Seq.empty, Seq.empty, Seq(xt.IsAbstract))
      val baseType = xt.ClassType(adt.id.asInstanceOf[stainless.ast.SymbolIdentifier], Seq.empty)
      idToClassMap(adt.id) = baseType
      classDefs = classDefs ++: adt.constructors.map { constructor =>
        val classType = xt.ClassType(constructor.id.asInstanceOf[stainless.ast.SymbolIdentifier], Seq.empty)
        idToClassMap(constructor.id) = classType
        new xt.ClassDef(constructor.id.asInstanceOf[stainless.ast.SymbolIdentifier],
          adt.tparams.asInstanceOf[Seq[xt.TypeParameterDef]],
          Seq(baseType), constructor.fields.map(patchDef(_).asInstanceOf[trees.ValDef]) /*.asInstanceOf[Seq[xt.ValDef]]*/ , Seq.empty
        )
      }
    }
    )

    var patchedFunctions = Seq.empty[trees.FunDef]

    functions.foreach(function =>
      patchedFunctions = patchedFunctions :+ patchFunction(function)
    )

    (patchedFunctions, classDefs)
  }
}
