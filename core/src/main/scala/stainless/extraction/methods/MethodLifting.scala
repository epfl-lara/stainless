/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import inox.utils.{NoPosition, Position}

trait MethodLifting extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: throwing.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import s._

    implicit val popts = new PrinterOptions(printUniqueIds = true, symbols = Some(symbols))

    for (fd <- symbols.functions.values) {
      import symbols._
      if (!isSubtypeOf(fd.fullBody.getType, fd.returnType)) {
        println(explainTyping(fd.fullBody)(PrinterOptions()))
      }
    }

    val children: Map[Identifier, Seq[Identifier]] =
      symbols.classes.values
        .flatMap(cd => cd.parents.map(_ -> cd))
        .groupBy(_._1.id)
        .mapValues(_.map(_._2.id).toSeq.sortBy(_.name))

    sealed trait Override { val cid: Identifier }
    case class FunOverride(cid: Identifier, fid: Option[Identifier], children: Seq[Override]) extends Override
    case class ValOverride(cid: Identifier, vd: ValDef) extends Override

    val (newSymbols, functionToOverrides): (Symbols, Map[Identifier, FunOverride]) = {
      val fieldOverrides: Map[(Identifier, String), ValOverride] = symbols.classes.values
        .flatMap(cd => cd.fields.map(vd => (cd.id, vd.id.name) -> ValOverride(cd.id, vd))).toMap

      def firstSymbol(cid: Identifier, vd: ValDef): Option[Symbol] = {
        val cd = symbols.getClass(cid)
        cd.methods(symbols).find { id =>
          val fd = symbols.getFunction(id)
          fd.tparams.isEmpty && fd.params.isEmpty && fd.id.name == vd.id.name
        }.map(_.symbol).orElse(cd.parents.reverse.view.flatMap(ct => firstSymbol(ct.id, vd)).headOption)
      }

      def rec(id: Identifier): Map[Symbol, Override] = {
        val cd = symbols.getClass(id)
        val cids = children.getOrElse(id, Seq.empty)
        val ctrees = if (cids.isEmpty) {
          Seq(cd.fields.flatMap(vd => firstSymbol(id, vd).map(_ -> ValOverride(id, vd))).toMap)
        } else {
          cids.map(rec)
        }

        val newOverrides = cd.methods(symbols).map { fid =>
          fid.symbol -> FunOverride(id, Some(fid), ctrees.flatMap(_.get(fid.symbol)))
        }.toMap

        val noOverrides = ctrees.flatMap(_.keys.toSet).filterNot(newOverrides contains _).map {
          sym => sym -> FunOverride(id, None, ctrees.flatMap(_.get(sym)))
        }

        newOverrides ++ noOverrides
      }

      def funs(o: Override): Map[Identifier, FunOverride] = o match {
        case fo @ FunOverride(_, fid, children) => children.flatMap(funs).toMap ++ fid.map(_ -> fo)
        case _ => Map.empty[Identifier, FunOverride]
      }

      symbols.classes.values
        .filter(_.parents.isEmpty)
        .flatMap(cd => rec(cd.id).map(p => (cd, p._1, p._2)))
        .foldLeft((symbols, Map.empty[Identifier, FunOverride])) {
          case ((symbols, mapping), (_, _, _: ValOverride)) => (symbols, mapping)
          case ((symbols, mapping), (cd, sym, o: FunOverride)) =>
            val fs = funs(o).toList
            val optInv = fs.filter(p => symbols.getFunction(p._1).flags contains IsInvariant) match {
              case ((id, FunOverride(_, optFid, _))) :: rest if o.fid.isEmpty =>
                val pos = optFid match {
                  case Some(fid) => symbols.getFunction(fid).getPos
                  case None => NoPosition
                }
                val fd = new FunDef(
                  id.freshen,
                  Seq.empty,
                  Seq.empty,
                  BooleanType(),
                  BooleanLiteral(true),
                  Seq(IsInvariant, IsMethodOf(cd.id))
                ).setPos(pos)
                Some(fd)

              case x :: xs => Some(symbols.getFunction(o.fid.get))
              case _ => None
            }

            val optCd = optInv.map(fd => cd.copy(flags = cd.flags :+ HasADTInvariant(fd.id)))
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
    class BaseTransformer extends oo.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = e match {
        case s.MethodInvocation(rec, id, tps, args) =>
          val s.ClassType(_, ctps) = newSymbols.widen(rec.getType(newSymbols))
          t.FunctionInvocation(id, (ctps ++ tps) map transform, (rec +: args) map transform).copiedFrom(e)

        case _ => super.transform(e)
      }
    }

    object default extends BaseTransformer

    def makeFunction(cid: Identifier, fid: Identifier, cos: Seq[Override]): t.FunDef = {
      val cd = newSymbols.getClass(cid)
      val fd = newSymbols.getFunction(fid)
      val tpSeq = newSymbols.freshenTypeParams(cd.typeArgs)
      val tpMap = (cd.typeArgs zip tpSeq).toMap

      val tcd = s.ClassType(cid, tpSeq).tcd(newSymbols).copiedFrom(cd)
      val arg = t.ValDef(FreshIdentifier("thiss"), default.transform(tcd.toType)).copiedFrom(tcd)

      object transformer extends BaseTransformer {
        override def transform(e: s.Expr): t.Expr = e match {
          case s.This(ct) => arg.toVariable
          case _ => super.transform(e)
        }

        override def transform(tpe: s.Type): t.Type = tpe match {
          case tp: s.TypeParameter if tpMap contains tp => super.transform(tpMap(tp))
          case _ => super.transform(tpe)
        }
      }

      val subCalls = (for (co <- cos) yield {
        firstOverrides(co).map { case (cid, either) =>
          val descendant = tcd.descendants.find(_.id == cid).get
          val descType = default.transform(descendant.toType).asInstanceOf[t.ClassType]
          val thiss = t.Annotated(t.AsInstanceOf(arg.toVariable, descType).copiedFrom(arg), Seq(t.Unchecked))

          def wrap(e: t.Expr, tpe: s.Type, expected: s.Type): t.Expr = 
            if (newSymbols.isSubtypeOf(tpe, expected)) e
            else t.AsInstanceOf(e, transformer.transform(expected)).copiedFrom(e)

          val (tpe, expr) = either match {
            case Left(nfd) =>
              val ntpMap = descendant.typeMap ++ (nfd.typeArgs zip fd.typeArgs)
              val args = (fd.params zip nfd.params).map { case (vd1, vd2) =>
                wrap(
                  transformer.transform(vd1.toVariable),
                  s.typeOps.instantiateType(vd1.tpe, tpMap),
                  s.typeOps.instantiateType(vd2.tpe, ntpMap)
                )
              }
              (
                s.typeOps.instantiateType(nfd.returnType, ntpMap),
                t.FunctionInvocation(
                  nfd.id,
                  descType.tps ++ fd.tparams.map(tdef => transformer.transform(tdef.tp)),
                  thiss +: args
                ).copiedFrom(fd)
              )
            case Right(vd) => (
              descendant.fields.find(_.id == vd.id).get.tpe,
              t.ClassSelector(thiss, vd.id).copiedFrom(fd)
            )
          }

          val expectedType = s.typeOps.instantiateType(fd.returnType, tpMap)
          (t.IsInstanceOf(arg.toVariable, descType).copiedFrom(arg), wrap(expr, tpe, expectedType))
        }
      }).flatten

      val returnType = transformer.transform(fd.returnType)

      val notFullyOverriden: Boolean = !(newSymbols.getClass(cid).flags contains IsSealed) || {
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

      val (specs, body) = exprOps.deconstructSpecs(fd.fullBody)(newSymbols)

      val (conds, elze) = if (subCalls.isEmpty || notFullyOverriden) {
        val elze = body match {
          case Some(body) => transformer.transform(body)
          case None => t.NoTree(returnType).copiedFrom(fd.fullBody)
        }
        (subCalls, elze)
      } else {
        val conds :+ ((_, elze: t.Expr)) = subCalls
        (conds, elze)
      }

      val newSpecs = specs.map(_.map(t)(transformer.transform(_)))
      val dispatchBody = conds.foldRight(elze) { case ((cond, res), elze) =>
        t.IfExpr(cond, res, elze).setPos(Position.between(cond.getPos, elze.getPos))
      }

      val newBody = if (!fd.flags.contains(IsInvariant)) dispatchBody else {
        // If `fd` is an invariant, we need to conjoin both the constructor's and parent's invariants,
        // otherwise we would only end up the checking the former.
        t.and(dispatchBody, elze.copiedFrom(dispatchBody))
      }

      val fullBody = t.exprOps.reconstructSpecs(newSpecs, Some(newBody), returnType)

      new t.FunDef(
        fd.id,
        (tpSeq.map(s.TypeParameterDef(_)) ++ fd.tparams) map transformer.transform,
        arg +: (fd.params map transformer.transform),
        returnType,
        fullBody,
        fd.flags filterNot (f => f == IsMethodOf(cid) || f == IsInvariant || f == IsAbstract) map transformer.transform
      ).copiedFrom(fd)
    }

    val functions: Seq[t.FunDef] = newSymbols.functions.values
      .map(fd => if (fd.flags exists { case IsMethodOf(_) => true case _ => false }) {
        val o = functionToOverrides(fd.id)
        makeFunction(o.cid, fd.id, o.children)
      } else {
        default.transform(fd)
      }).toSeq

    val classes: Seq[t.ClassDef] = newSymbols.classes.values
      .map(cd => default.transform(cd)).toSeq

    t.NoSymbols.withFunctions(functions).withClasses(classes)
  }
}
