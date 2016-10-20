/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate
package oo

trait MethodLifting extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: holes.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._
    import symbols._

    val children: Map[Identifier, Set[Identifier]] =
      symbols.classes.values
        .filter(_.parent.isDefined)
        .groupBy(_.parent.get)
        .mapValues(_.map(_.id).toSet)

    val descendants: Map[Identifier, Set[Identifier]] =
      inox.utils.fixpoint { (map: Map[Identifier, Set[Identifier]]) =>
        map.map { case (p, desc) => p -> (desc ++ desc.flatMap(map.getOrElse(_, Set.empty))) }
      } (children)

    val classToParent: Map[Identifier, Identifier] = symbols.classes.values.map(cd => cd.id -> cd.root.id).toMap
    val classToConstructors: Map[Identifier, Set[Identifier]] = {
      def rec(id: Identifier): Set[Identifier] = {
        val cs = children.getOrElse(id, Set.empty)
        if (cs.isEmpty) Set(id) else cs.flatMap(rec)
      }
      symbols.classes.values.map(cd => cd.id -> rec(cd.id)).toMap
    }

    def approximate(id: Identifier) = if (classToConstructors(id) == Set(id)) id else classToParent(id)

    def conditionFor(id: Identifier, v: t.Variable): t.Expr = {
      val cons = classToConstructors(id)
      if (classToConstructors(classToParent(id)) == cons) {
        t.BooleanLiteral(true)
      } else {
        val t.ADTType(_, tps) = v.tpe
        cons.toSeq.map(id => t.IsInstanceOf(v, t.ADTType(id, tps))) match {
          case Seq() => t.BooleanLiteral(true)
          case Seq(elem) => elem
          case multiple => t.And(multiple)
        }
      }
    }

    class Override(val cid: Identifier, val fid: Option[Identifier], val children: Set[Override])

    val functionToOverrides: Map[Identifier, Override] = {
      def rec(id: Identifier): Map[Symbol, Override] = {
        val ctrees = children.getOrElse(id, Set.empty).map(rec)
        val newOverrides = symbols.getClass(id).methods.map {
          fid => fid.symbol -> new Override(id, Some(fid), ctrees.flatMap(_.get(fid.symbol)))
        }.toMap

        val noOverrides = (ctrees.flatMap(_.keys.toSet) -- newOverrides.keys).map {
          sym => sym -> new Override(id, None, ctrees.flatMap(_.get(sym)))
        }

        newOverrides ++ noOverrides
      }

      def funs(o: Override): Map[Identifier, Override] =
        (if (o.fid.isDefined) Map(o.fid.get -> o) else Map.empty) ++ o.children.toSet.flatMap(funs)

      (for {
        cd <- symbols.classes.values if cd.parent.isEmpty
        (sym, o) <- rec(cd.id)
        (id, o) <- funs(o)
      } yield id -> o).toMap
    }

    def firstFunctions(o: Override): Set[(Identifier, FunDef)] = o.fid match {
      case Some(id) => Set(o.cid -> symbols.getFunction(id))
      case None => o.children.toSet.flatMap(firstFunctions)
    }

    // @nv: this has to be a class for some weird reason, otherwise the scala compiler
    //      will give you random errors until you set fire to yourself
    class BaseTransformer extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      object deconstructor extends holes.TreeDeconstructor {
        protected val s: self.s.type = self.s
        protected val t: self.t.type = self.t
      }

      override def transform(e: s.Expr): t.Expr = e match {
        case s.MethodInvocation(rec, id, tps, args) =>
          val s.ClassType(_, ctps) = rec.getType(symbols)
          t.FunctionInvocation(id, (ctps ++ tps) map transform, (rec +: args) map transform)

        case s.ClassConstructor(ct: s.ClassType, args) =>
          val tpe = transform(ct).asInstanceOf[t.ADTType]
          t.ADT(tpe, args map transform)

        case s.ClassSelector(expr, selector) =>
          t.ADTSelector(transform(expr), selector)

        case _ => super.transform(e)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case s.ClassType(id, tps) => t.ADTType(approximate(id), tps map transform)
        case _ => super.transform(tpe)
      }
    }

    def makeFunction(cid: Identifier, fid: Identifier, children: Set[Override]): t.FunDef = {
      val fd = getFunction(fid)
      val adtTparams = symbols.getClass(cid).tparams.map(_.freshen)
      val arg = t.ValDef(
        FreshIdentifier("thiss"),
        t.ADTType(approximate(cid), adtTparams.map(tdef => t.TypeParameter(tdef.id)))
      )

      object transformer extends BaseTransformer {
        override def transform(e: s.Expr): t.Expr = e match {
          case s.This(ct) => arg.toVariable
          case _ => super.transform(e)
        }
      }

      val pre = conditionFor(cid, arg.toVariable)

      val subCalls = (for (co <- children.toSeq) yield {
        firstFunctions(co).toSeq.map { case (cid, nfd) =>
          (conditionFor(cid, arg.toVariable), t.FunctionInvocation(
            nfd.id,
            (adtTparams ++ fd.tparams).map(tdef => transformer.transform(tdef.tp)),
            arg.toVariable +: fd.params.map(vd => transformer.transform(vd.toVariable))
          ))
        }
      }).flatten

      val returnType = transformer.transform(fd.returnType)

      def fullyOverrides(o: Override): Boolean = o.fid.nonEmpty || o.children.forall(fullyOverrides)

      val (conds, elze) = if (children.exists(co => !fullyOverrides(co))) {
        val elze = fd.body match {
          case Some(body) => transformer.transform(body)
          case None => t.NoTree(returnType)
        }
        (subCalls, elze)
      } else {
        val conds :+ ((_, elze: t.Expr)) = subCalls
        (conds, elze)
      }

      val precondition = exprOps.preconditionOf(fd.fullBody) match {
        case Some(p) => Some(t.And(transformer.transform(p), pre))
        case None => Some(pre)
      }

      val body = conds.foldRight(elze) { case ((cond, res), elze) => t.IfExpr(cond, res, elze) }
      val postcondition = exprOps.postconditionOf(fd.fullBody).map(transformer.transform)
      val fullBody = t.exprOps.withPostcondition(
        t.exprOps.withPrecondition(body, precondition),
        postcondition.map(_.asInstanceOf[t.Lambda])
      )

      new t.FunDef(
        fd.id,
        transformer.transformTypeParams(adtTparams ++ fd.tparams),
        arg +: fd.params.map(transformer.transform),
        returnType,
        body,
        (fd.flags - s.IsMethod) map transformer.transform
      )
    }

    object transformer extends BaseTransformer

    val sorts: Seq[t.ADTSort] = symbols.classes.values
      .filter(cd => cd.parent.isEmpty && children.getOrElse(cd.id, Set.empty).nonEmpty)
      .map(cd => new t.ADTSort(
        cd.id,
        transformer.transformTypeParams(cd.tparams),
        classToConstructors(cd.id).toSeq,
        cd.flags map transformer.transform
      )).toSeq

    val cons: Seq[t.ADTConstructor] = symbols.classes.values
      .filter(cd => children.getOrElse(cd.id, Set.empty).isEmpty)
      .map(cd => new t.ADTConstructor(
        cd.id,
        transformer.transformTypeParams(cd.tparams),
        if (classToParent(cd.id) == cd.id) None else Some(classToParent(cd.id)),
        cd.fields map transformer.transform,
        cd.flags map transformer.transform
      )).toSeq

    val functions: Seq[t.FunDef] = symbols.functions.values
      .map(fd => if (fd.flags(IsMethod)) {
        val o = functionToOverrides(fd.id)
        makeFunction(o.cid, fd.id, o.children)
      } else {
        transformer.transform(fd)
      }).toSeq

    t.NoSymbols.withFunctions(functions).withADTs(sorts ++ cons)
  }
}
