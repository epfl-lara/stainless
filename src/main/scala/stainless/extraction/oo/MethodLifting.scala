/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

trait MethodLifting extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: holes.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._

    val children: Map[Identifier, Set[Identifier]] =
      symbols.classes.values
        .filter(_.parent.isDefined)
        .groupBy(_.parent.get)
        .mapValues(_.map(_.id).toSet)

    val descendants: Map[Identifier, Set[Identifier]] =
      inox.utils.fixpoint { (map: Map[Identifier, Set[Identifier]]) =>
        map.map { case (p, desc) => p -> (desc ++ desc.flatMap(map.getOrElse(_, Set.empty))) }
      } (children)

    val classToParent: Map[Identifier, Identifier] = symbols.classes.values.map {
      cd => cd.id -> cd.root(symbols).id
    }.toMap

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
        val t.ADTType(aid, tps) = v.tpe
        if (id == aid) {
          t.BooleanLiteral(true)
        } else cons.toSeq.map(id => t.IsInstanceOf(v, t.ADTType(id, tps))) match {
          case Seq() => t.BooleanLiteral(true)
          case Seq(elem) => elem
          case multiple => t.And(multiple)
        }
      }
    }

    sealed trait Override { val cid: Identifier }
    case class FunOverride(cid: Identifier, fid: Option[Identifier], children: Set[Override]) extends Override
    case class ValOverride(cid: Identifier, vd: ValDef) extends Override

    val (newSymbols, functionToOverrides): (Symbols, Map[Identifier, FunOverride]) = {
      val fieldOverrides: Map[(Identifier, String), ValOverride] = symbols.classes.values
        .flatMap(cd => cd.fields.map(vd => (cd.id, vd.id.name) -> ValOverride(cd.id, vd))).toMap

      def firstSymbol(cid: Identifier, vd: ValDef): Option[Symbol] = {
        val cd = symbols.getClass(cid)
        cd.methods.find { id =>
          val fd = symbols.getFunction(id)
          fd.tparams.isEmpty && fd.params.isEmpty && fd.id.name == vd.id.name
        }.map(_.symbol).orElse(cd.parent.flatMap(firstSymbol(_, vd)))
      }

      def rec(id: Identifier): Map[Symbol, Override] = {
        val cd = symbols.getClass(id)
        val cids = children.getOrElse(id, Set.empty)
        val ctrees = if (cids.isEmpty) {
          Set(cd.fields.flatMap(vd => firstSymbol(id, vd).map(_ -> ValOverride(id, vd))).toMap)
        } else {
          cids.map(rec)
        }

        val newOverrides = cd.methods.map { fid =>
          fid.symbol -> FunOverride(id, Some(fid), ctrees.flatMap(_.get(fid.symbol)))
        }.toMap

        val noOverrides = (ctrees.flatMap(_.keys.toSet) -- newOverrides.keys).map {
          sym => sym -> FunOverride(id, None, ctrees.flatMap(_.get(sym)))
        }

        newOverrides ++ noOverrides
      }

      def funs(o: Override): Map[Identifier, FunOverride] = o match {
        case fo @ FunOverride(_, fid, children) => children.flatMap(funs).toMap ++ fid.map(_ -> fo)
        case _ => Map.empty[Identifier, FunOverride]
      }

      symbols.classes.values
        .filter(_.parent.isEmpty)
        .flatMap(cd => rec(cd.id).map(p => (cd, p._1, p._2)))
        .foldLeft((symbols, Map.empty[Identifier, FunOverride])) {
          case ((symbols, mapping), (_, _, _: ValOverride)) => (symbols, mapping)
          case ((symbols, mapping), (cd, sym, o: FunOverride)) =>
            val fs = funs(o).toList
            val optInv = fs.filter(p => symbols.getFunction(p._1).flags contains IsInvariant) match {
              case ((id, _)) :: rest if o.fid.isEmpty => Some(new FunDef(
                id.freshen,
                Seq.empty,
                Seq.empty,
                BooleanType,
                BooleanLiteral(true),
                Set(IsInvariant, IsMethod)
              ))

              case x :: xs => Some(symbols.getFunction(o.fid.get))
              case _ => None
            }

            val optCd = optInv.map(fd => cd.copy(flags = cd.flags + HasADTInvariant(fd.id)))
            val newSymbols = symbols.withFunctions(optInv.toSeq).withClasses(optCd.toSeq)
            val newMapping = mapping ++ fs ++ optInv.map(fd => fd.id -> o.copy(fid = Some(fd.id)))

            (newSymbols, newMapping)
        }
    }

    def firstOverrides(o: Override): Seq[(Identifier, Either[FunDef, ValDef])] = o match {
      case FunOverride(cid, Some(id), _) => Seq(cid -> Left(newSymbols.getFunction(id)))
      case FunOverride(_, _, children) => children.toSeq.flatMap(firstOverrides)
      case ValOverride(cid, vd) => Seq(cid -> Right(vd))
    }

    // @nv: this has to be a class for some weird reason, otherwise the scala compiler
    //      will give you random errors until you set fire to yourself
    class BaseTransformer extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = e match {
        case s.MethodInvocation(rec, id, tps, args) =>
          val s.ClassType(_, ctps) = rec.getType(newSymbols)
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

    object default extends BaseTransformer

    def makeFunction(cid: Identifier, fid: Identifier, cos: Set[Override]): t.FunDef = {
      val fd = newSymbols.getFunction(fid)
      val tparamsSeq = newSymbols.getClass(cid).tparams.map(tp => tp -> tp.freshen)
      val adtTparams = tparamsSeq.map(_._2)
      val tparamsMap = tparamsSeq.map(p => p._1.tp -> p._2.tp).toMap

      val aid = approximate(cid)
      val tps = adtTparams.map(tdef => default.transform(tdef).tp)
      val arg = t.ValDef(FreshIdentifier("thiss"), t.ADTType(aid, tps), Set.empty)

      object transformer extends BaseTransformer {
        override def transform(e: s.Expr): t.Expr = e match {
          case s.This(ct) => arg.toVariable
          case _ => super.transform(e)
        }

        override def transform(tpe: s.Type): t.Type = tpe match {
          case tp: s.TypeParameter if tparamsMap contains tp => super.transform(tparamsMap(tp))
          case _ => super.transform(tpe)
        }
      }

      val pre = conditionFor(cid, arg.toVariable)

      val subCalls = (for (co <- cos.toSeq) yield {
        firstOverrides(co).toSeq.map { case (cid, either) =>
          val thiss = if (aid != cid && classToConstructors(cid) == Set(cid)) {
            t.AsInstanceOf(arg.toVariable, t.ADTType(cid, tps))
          } else {
            arg.toVariable
          }

          (conditionFor(cid, arg.toVariable), either match {
            case Left(nfd) => t.FunctionInvocation(
              nfd.id,
              (adtTparams ++ fd.tparams).map(tdef => transformer.transform(tdef.tp)),
              thiss +: fd.params.map(vd => transformer.transform(vd.toVariable))
            )
            case Right(vd) => t.ADTSelector(thiss, vd.id)
          })
        }
      }).flatten

      val returnType = transformer.transform(fd.returnType)

      val notFullyOverriden: Boolean = {
        def rec(o: Override): Boolean = o match {
          case FunOverride(_, Some(_), _) => true
          case FunOverride(_, _, children) => children.forall(rec)
          case ValOverride(_, _) => true
        }

        val coMap = cos.map(co => co.cid -> co).toMap
        children.getOrElse(cid, Set.empty).exists {
          ccid => !(coMap contains ccid) || !rec(coMap(ccid))
        }
      }

      val (conds, elze) = if (subCalls.isEmpty || notFullyOverriden) {
        val elze = fd.body(newSymbols) match {
          case Some(body) => transformer.transform(body)
          case None => t.NoTree(returnType)
        }
        (subCalls, elze)
      } else {
        val conds :+ ((_, elze: t.Expr)) = subCalls
        (conds, elze)
      }

      val precondition = (exprOps.preconditionOf(fd.fullBody) match {
        case Some(p) => Some(t.And(transformer.transform(p), pre))
        case None => Some(pre)
      }).filterNot(_ == t.BooleanLiteral(true))

      val body = conds.foldRight(elze) { case ((cond, res), elze) => t.IfExpr(cond, res, elze) }
      val postcondition = exprOps.postconditionOf(fd.fullBody).map(transformer.transform)
      val fullBody = t.exprOps.withPostcondition(
        t.exprOps.withPrecondition(body, precondition),
        postcondition.map(_.asInstanceOf[t.Lambda])
      )

      new t.FunDef(
        fd.id,
        (adtTparams ++ fd.tparams) map transformer.transform,
        arg +: (fd.params map transformer.transform),
        returnType,
        fullBody,
        (fd.flags - IsMethod - IsInvariant - IsAbstract) map transformer.transform
      )
    }

    val sortClasses = newSymbols.classes.values
      .filter(cd => cd.parent.isEmpty && children.getOrElse(cd.id, Set.empty).nonEmpty)

    for (cd <- sortClasses if !(cd.flags contains IsAbstract)) {
      throw MissformedStainlessCode(cd, "Non-abstract sort")
    }

    val sorts: Seq[t.ADTSort] = sortClasses.map(cd => new t.ADTSort(
      cd.id,
      cd.tparams map default.transform,
      classToConstructors(cd.id).toSeq,
      (cd.flags - IsAbstract) map default.transform
    )).toSeq

    val consClasses = newSymbols.classes.values
      .filter(cd => children.getOrElse(cd.id, Set.empty).isEmpty)

    for (cd <- consClasses if cd.flags contains IsAbstract) {
      throw MissformedStainlessCode(cd, "Abstract constructor")
    }

    val cons: Seq[t.ADTConstructor] = consClasses.map(cd => new t.ADTConstructor(
      cd.id,
      cd.tparams map default.transform,
      if (classToParent(cd.id) == cd.id) None else Some(classToParent(cd.id)),
      cd.fields map default.transform,
      cd.flags map default.transform
    )).toSeq

    val functions: Seq[t.FunDef] = newSymbols.functions.values
      .map(fd => if (fd.flags(IsMethod)) {
        val o = functionToOverrides(fd.id)
        makeFunction(o.cid, fd.id, o.children)
      } else {
        default.transform(fd)
      }).toSeq

    t.NoSymbols.withFunctions(functions).withADTs(sorts ++ cons)
  }
}
