/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._

trait TypeEncoding extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: holes.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import t._
    import t.dsl._

    /* Identifier for the base `Type` sort */
    val tpeID = FreshIdentifier("Type")
    val tpe  = T(tpeID)()


    /* ====================================
     *           TYPE SEQUENCE
     * ====================================
     *
     * Corresponds to the following ADT definition:
     * {{{
     * sealed abstract class Seq
     * case class Cons(head: Type, tail: Seq) extends Seq
     * case object Nil extends Seq
     * }}}
     *
     * This is used to define types with variable number
     * of type parameters, such as class-types, adt-types,
     * tuple types and function types.
     */
    val seqID  = FreshIdentifier("Seq")
    val consID = FreshIdentifier("Cons")
    val nilID  = FreshIdentifier("Nil")

    val head = FreshIdentifier("head")
    val tail = FreshIdentifier("tail")

    val seq  = T(seqID)()
    val cons = T(consID)()
    val nil  = T(nilID)()

    def mkSeq(es: Seq[Expr]): Expr = es.foldRight(nil())((h, t) => cons(h, t))

    val seqSort  = mkSort(seqID)()(Seq(consID, nilID))
    val consCons = mkConstructor(consID)()(Some(seqID))(_ => Seq(ValDef(head, tpe), ValDef(tail, seq)))
    val nilCons  = mkConstructor(nilID)()(Some(seqID))(_ => Seq())


    /* ====================================
     *           TYPE ADTS
     * ==================================== */

    val tpeSort = mkSort(tpeID)()(Seq(
      botID, topID, clsID, adtID, arrID,
      setID, bagID, mapID, tplID, funID
    ))

    /* Bottom type, corresponds to Scala's {{{Nothing}}} */
    val botID = FreshIdentifier("Bot")
    val botCons = mkConstructor(botID)()(Some(tpeID))(_ => Seq())
    val bot = T(botID)()

    /* Top type, corresponds to Scala's {{{Any}}} */
    val topID = FreshIdentifier("Top")
    val topCons = mkConstructor(topID)()(Some(tpeID))(_ => Seq())
    val top = T(topID)()

    /* Class type, corresponds to a class definition in Scala:
     * {{{
     * class A[T1,...,Tn] extends C1[Ti,...,Tj] with ... with CN[Tk,...,Tl]
     * }}}
     * Note that `T1` to `Tn` can be variant and have type bounds. */
    val clsID = FreshIdentifier("Class")
    val clsPtr = FreshIdentifier("id")  // `id` field, corresponds to `A` name
    val clsTps = FreshIdentifier("tps") // `tps` field, corresponds to `T1,...,Tn` type parameters
    val clsCons = mkConstructor(clsID)()(Some(tpeID))(_ => Seq(ValDef(clsPtr, IntegerType), ValDef(clsTps, seq)))
    val cls = T(clsID)()

    /* ADT type, corresponds to a datatype definition in Scala:
     * {{{
     * case class A[T1,...,Tn] extends B[T1,...,Tn]
     * }}}
     * Note that `T1` to `Tn` must be invariant here. */
    val adtID = FreshIdentifier("Adt")
    val adtPtr = FreshIdentifier("id")  // `id` field, corresponds to `A` name
    val adtTps = FreshIdentifier("tps") // `tps` field, corresponds to `T1,...,Tn` type parameters
    val adtCons = mkConstructor(adtID)()(Some(tpeID))(_ => Seq(ValDef(adtPtr, IntegerType), ValDef(adtTps, seq)))
    val adt = T(adtID)()

    /* Array type, corresponds to {{{Array[base]}}} in Scala */
    val arrID = FreshIdentifier("Array")
    val arrBase = FreshIdentifier("base") // `base` field in `Array[base]` type
    val arrCons = mkConstructor(arrID)()(Some(tpeID))(_ => Seq(ValDef(arrBase, tpe)))
    val arr = T(arrID)()

    /* Set type, corresponds to {{{Set[base]}}} in Scala */
    val setID = FreshIdentifier("Set")
    val setBase = FreshIdentifier("base") // `base` field in `Set[base]` type
    val setCons = mkConstructor(setID)()(Some(tpeID))(_ => Seq(ValDef(setBase, tpe)))
    val set = T(setID)()

    /* Bag type, corresponds to {{{Bag[base]}}} in Scala */
    val bagID = FreshIdentifier("Bag")
    val bagBase = FreshIdentifier("base") // `base` field in `Bag[base]` type
    val bagCons = mkConstructor(bagID)()(Some(tpeID))(_ => Seq(ValDef(bagBase, tpe)))
    val bag = T(bagID)()

    /* Map type, corresponds to {{{Map[from,to}}} in Scala */
    val mapID = FreshIdentifier("Map")
    val mapFrom = FreshIdentifier("from") // `from` field in `Map[from,to]` type
    val mapTo   = FreshIdentifier("to")   // `to`   field in `Map[from,to]` type
    val mapCons = mkConstructor(mapID)()(Some(tpeID))(_ => Seq(ValDef(mapFrom, tpe), ValDef(mapTo, tpe)))
    val map = T(mapID)()

    /* Tuple type, corresponds to {{{(Type1,...,TypeN)}}} in Scala */
    val tplID = FreshIdentifier("Tuple")
    val tplTps = FreshIdentifier("tps") // `tps` field in `(tps1,...,tpsN)` type
    val tplCons = mkConstructor(tplID)()(Some(tpeID))(_ => Seq(ValDef(tplTps, seq)))
    val tpl = T(mapID)()

    /* Function type, corresponds to {{{(From1,...,FromN) => To}}} in Scala */
    val funID = FreshIdentifier("Function")
    val funFrom = FreshIdentifier("from") // `from` field in `(from1,...,fromN) => to` type
    val funTo   = FreshIdentifier("to")   // `to`   field in `(from1,...,fromN) => to` type
    val funCons = mkConstructor(funID)()(Some(tpeID))(_ => Seq(ValDef(funFrom, seq), ValDef(funTo, tpe)))
    val fun = T(mapID)()


    /* ====================================
     *         SUBTYPING FUNCTION
     * ==================================== */

    val subtypeID = FreshIdentifier("isSubtypeOf")
    val subtypeOf = E(subtypeID)()

    val subtypeFunction = mkFunDef(subtypeID)()(_ => (
      Seq("tp1" :: tpe, "tp2" :: tpe), BooleanType, {
        case Seq(tp1, tp2) => Seq(
          tp2.isInstOf(top) -> E(true),
          tp1.isInstOf(bot) -> E(true),
          tp1.isInstOf(cls) -> (throw new Exception("TODO")),
          tp1.isInstOf(adt) -> (throw new Exception("TODO")),
          tp1.isInstOf(arr) -> (
            tp2.isInstOf(arr) &&
            tp1.asInstOf(arr).getField(arrBase) === tp2.asInstOf(arr).getField(arrBase)
          ),
          tp1.isInstOf(set) -> (
            tp2.isInstOf(set) &&
            tp1.asInstOf(set).getField(setBase) === tp2.asInstOf(set).getField(setBase)
          ),
          tp1.isInstOf(bag) -> (
            tp2.isInstOf(bag) &&
            tp1.asInstOf(bag).getField(bagBase) === tp2.asInstOf(bag).getField(bagBase)
          ),
          tp1.isInstOf(map) -> (
            tp2.isInstOf(map) &&
            tp1.asInstOf(map).getField(mapFrom) === tp2.asInstOf(map).getField(mapFrom) &&
            tp1.asInstOf(map).getField(mapTo) === tp2.asInstOf(map).getField(mapTo)
          ),
          tp1.isInstOf(tpl) -> (
            tp2.isInstOf(tpl) && (
              (
                tp1.asInstOf(tpl).getField(tplTps).isInstOf(nil) &&
                tp2.asInstOf(tpl).getField(tplTps).isInstOf(nil)
              ) || (
                tp1.asInstOf(tpl).getField(tplTps).isInstOf(cons) &&
                tp2.asInstOf(tpl).getField(tplTps).isInstOf(cons) &&
                subtypeOf(
                  tp1.asInstOf(tpl).getField(tplTps).asInstOf(cons).getField(head),
                  tp2.asInstOf(tpl).getField(tplTps).asInstOf(cons).getField(head)
                ) &&
                subtypeOf(
                  tpl(tp1.asInstOf(tpl).getField(tplTps).asInstOf(cons).getField(tail)),
                  tpl(tp2.asInstOf(tpl).getField(tplTps).asInstOf(cons).getField(tail))
                )
              )
            )
          ),
          tp1.isInstOf(fun) -> (
            tp2.isInstOf(fun) && (
              (
                tp1.asInstOf(fun).getField(funFrom).isInstOf(nil) &&
                tp2.asInstOf(fun).getField(funFrom).isInstOf(nil) &&
                subtypeOf(
                  tp1.asInstOf(fun).getField(funTo),
                  tp2.asInstOf(fun).getField(funTo)
                )
              ) || (
                tp1.asInstOf(fun).getField(funFrom).isInstOf(cons) &&
                tp2.asInstOf(fun).getField(funFrom).isInstOf(cons) &&
                subtypeOf( // contravariant!
                  tp2.asInstOf(fun).getField(funFrom).asInstOf(cons).getField(head),
                  tp1.asInstOf(fun).getField(funFrom).asInstOf(cons).getField(head)
                ) &&
                subtypeOf(
                  fun(
                    tp1.asInstOf(fun).getField(funFrom).asInstOf(cons).getField(tail),
                    tp1.asInstOf(fun).getField(funTo)
                  ),
                  fun(
                    tp2.asInstOf(fun).getField(funFrom).asInstOf(cons).getField(tail),
                    tp2.asInstOf(fun).getField(funTo)
                  )
                )
              )
            )
          )
        ).foldRight(E(false): Expr) {
          case ((cond, thenn), elze) => IfExpr(cond, thenn, elze)
        }
      }))

    def isSimple(tpe: s.Type): Boolean = !s.typeOps.exists {
      case s.NothingType | s.AnyType => true
      case (_: s.ClassType) | (_: s.TypeBounds) => true
      case (_: s.UnionType) | (_: s.IntersectionType) => true
      case _ => false
    } (tpe)

    object identity extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
    }


    /* ====================================
     *             REF-TYPES ADT
     * ==================================== */

    val objID = FreshIdentifier("Object")
    val objTpe = FreshIdentifier("getType")
    val objCons = mkConstructor(objID)()(None)(_ => Seq(ValDef(objTpe, tpe)))
    val obj = T(objID)()

    val typeField = FreshIdentifier("getType")
    val typeFunction = mkFunDef(typeField)()(_ => (
      Seq("e" :: obj), tpe, { case Seq(e) => choose("res" :: tpe)(_ => E(true)) }))

    def getType(e: t.Expr): t.Expr = E(typeField)()(e)

    val classFields = symbols.classes.values.flatMap { cls =>
      cls.fields.map { vd =>
        val id = vd.id.freshen
        val fieldFunction = mkFunDef(id)()(_ => (
          Seq("e" :: obj),
          if (isSimple(vd.tpe)) identity.transform(vd.tpe) else tpe,
          { case Seq(e) => choose("res" :: tpe)(_ => E(true)) }
        ))
        vd.id -> fieldFunction
      }
    }.toMap

    def getField(e: t.Expr, id: Identifier): t.Expr = E(classFields(id).id)()(e)


    /* ====================================
     *      FUNCTION TRANSFORMATION
     * ==================================== */

    def guardForCase(scrut: s.Expr, pattern: s.Pattern): (s.Pattern, Option[s.Expr]) = {
      import s._
      import symbols._

      def rec(in: Expr, pattern: Pattern): (Pattern, Expr) = pattern match {
        case WildcardPattern(ob) => (pattern, BooleanLiteral(true))

        case InstanceOfPattern(ob, tpe) =>
          if (isSimple(leastUpperBound(in.getType, tpe))) {
            (pattern, BooleanLiteral(true))
          } else {
            val v = ob.map(_.toVariable).getOrElse(in)
            (WildcardPattern(ob), IsInstanceOf(v, tpe))
          }

        case ClassPattern(ob, ct, subs) =>
          val v = ob.map(_.toVariable).getOrElse(in)
          val rsubs = (ct.tcd.fields zip subs).map(p => rec(ClassSelector(asInstOf(v, ct), p._1.id), p._2))
          (ClassPattern(ob, ct, rsubs.map(_._1)), andJoin(rsubs.map(_._2)))

        case ADTPattern(ob, adt, subs) =>
          val tcons = adt.getADT.toConstructor
          val v = ob.map(_.toVariable).getOrElse(in)
          val rsubs = (tcons.fields zip subs).map(p => rec(adtSelector(asInstOf(v, adt), p._1.id), p._2))
          (ADTPattern(ob, adt, rsubs.map(_._1)), andJoin(rsubs.map(_._2)))

        case TuplePattern(ob, subs) =>
          val v = ob.map(_.toVariable).getOrElse(in)
          val rsubs = subs.zipWithIndex.map(p => rec(tupleSelect(v, p._2 + 1, subs.size), p._1))
          (TuplePattern(ob, rsubs.map(_._1)), andJoin(rsubs.map(_._2)))

        case up @ UnapplyPattern(ob, id, tps, subs) =>
          val rsubs = (unwrapTuple(up.get(in), subs.size) zip subs) map (rec _).tupled
          (UnapplyPattern(ob, id, tps, rsubs.map(_._1)), andJoin(rsubs.map(_._2)))

        case LiteralPattern(ob, lit) =>
          if (isSimple(leastUpperBound(in.getType, lit.getType))) {
            (pattern, BooleanLiteral(true))
          } else {
            val v = ob.map(_.toVariable).getOrElse(in)
            (WildcardPattern(ob), Equals(v, lit))
          }
      }

      val (newPattern, cond) = rec(scrut, pattern)
      (newPattern, cond match {
        case s.BooleanLiteral(true) => None
        case _ => Some(cond)
      })
    }

    def isSimpleFunction(fun: s.FunAbstraction): Boolean = {
      import symbols._

      var simple: Boolean = true
      object traverser extends s.TreeTraverser {
        override def traverse(e: s.Expr): Unit = e match {
          case s.ClassConstructor(_, _) => simple = false
          case s.ClassSelector(_, _) => simple = false
          case s.MatchExpr(scrut, cases) if cases.exists {
            case s.MatchCase(pat, _, _) => guardForCase(scrut, pat) != (pat, None)
          } => simple = false
          case s.IsInstanceOf(e, tpe) if !isSimple(leastUpperBound(e.getType, tpe)) => simple = false
          case s.AsInstanceOf(e, tpe) if !isSimple(leastUpperBound(e.getType, tpe)) => simple = false
          case _ => super.traverse(e)
        }

        override def traverse(tpe: s.Type): Unit = tpe match {
          case s.ClassType(_, _) => simple = false
          case _ => super.traverse(tpe)
        }

        override def traverse(pat: s.Pattern): Unit = pat match {
          case s.ClassPattern(_, _, _) => simple = false
          case _ => super.traverse(pat)
        }
      }

      fun.tparams.foreach(traverser.traverse)
      fun.params.foreach(traverser.traverse)
      traverser.traverse(fun.returnType)
      traverser.traverse(fun.fullBody)
      fun.flags.foreach(traverser.traverse)
      simple
    }

    class Scope private(
      functions: Map[Identifier, s.FunAbstraction],
      val tparams: Map[s.TypeParameter, t.Expr],
      graph: DiGraph[s.FunAbstraction, SimpleEdge[s.FunAbstraction]],
      val simple: Set[Identifier]) {

      def withFunctions(funs: Seq[s.FunAbstraction]): Scope = {
        val newFunctions = functions ++ funs.map(fun => fun.id -> fun)

        var newGraph = graph
        for (fun1 <- funs; fun2 <- s.exprOps.collect {
          case s.FunInvocation(id, tps, args, _) => Set(newFunctions(id))
          case _ => Set[s.FunAbstraction]()
        } (fun1.fullBody)) newGraph += SimpleEdge(fun1, fun2)

        val baseSimple = funs.filter(isSimpleFunction).toSet
        val fixSimple = inox.utils.fixpoint { (funs: Set[s.FunAbstraction]) =>
          funs.filter(fun => newGraph.transitiveSucc(fun) subsetOf funs)
        } (baseSimple)

        val newSimple = simple ++ fixSimple.map(_.id)

        new Scope(newFunctions, tparams, newGraph, newSimple)
      }

      def in(fun: s.FunAbstraction): Scope = {
        val tparamsVars = fun.tparams.map(tpd => t.ValDef(tpd.id.freshen, tpe))
        val newTParams = tparams ++ (fun.tparams.map(_.tp) zip tparamsVars.map(_.toVariable))
        new Scope(functions, newTParams, graph, simple)
      }
    }

    object Scope {
      def empty = new Scope(Map.empty, Map.empty, new DiGraph, Set.empty)
    }

    def encodeType(tpe: s.Type)(implicit scope: Scope): t.Expr = tpe match {
      case s.AnyType => top()
      case s.NothingType => bot()
      case s.ClassType(id, tps) => cls(IntegerLiteral(id.globalId), mkSeq(tps map encodeType))
      case s.ADTType(id, tps) => adt(IntegerLiteral(id.globalId), mkSeq(tps map encodeType))
      case s.ArrayType(base) => arr(encodeType(base))
      case s.SetType(base) => set(encodeType(base))
      case s.BagType(base) => bag(encodeType(base))
      case s.MapType(from, to) => map(encodeType(from), encodeType(to))
      case s.TupleType(tps) => tpl(mkSeq(tps map encodeType))
      case s.FunctionType(from, to) => fun(mkSeq(from map encodeType), encodeType(to))
      case tp: s.TypeParameter => scope.tparams(tp)
      case _ => scala.sys.error("Unexpected type " + tpe)
    }

    def transformExpr(e: s.Expr)(implicit scope: Scope): t.Expr = {
      object transformer extends ast.TreeTransformer {
        val s: self.s.type = self.s
        val t: self.t.type = self.t

        override def transform(e: s.Expr): t.Expr = e match {
          case s.ClassConstructor(ct, args) =>
            choose("res" :: IntegerType) { res =>
              getType(res) === encodeType(ct) &&
              andJoin((ct.tcd(symbols).fields zip args).map(p => getField(res, p._1.id) === transform(p._2)))
            }

          case s.ClassSelector(expr, id) =>
            getField(transform(expr), id)

          case s.IsInstanceOf(expr, tpe) if !isSimple(symbols.leastUpperBound(expr.getType(symbols), tpe)) =>
            subtypeOf(getType(transform(expr)), encodeType(tpe))

          case s.AsInstanceOf(expr, tpe) if !isSimple(symbols.leastUpperBound(expr.getType(symbols), tpe)) =>
            // TODO: unwrap if isSimple(tpe)!!
            transform(s.Assert(
              s.IsInstanceOf(expr, tpe),
              Some("Cast error"),
              expr
            ))

          case s.MatchExpr(scrut, cases) =>
            super.transform(s.MatchExpr(scrut, for (cse <- cases) yield {
              val (newPattern, newGuard) = guardForCase(scrut, cse.pattern)
              val guard = s.andJoin(cse.optGuard.toSeq ++ newGuard) match {
                case s.BooleanLiteral(true) => None
                case cond => Some(cond)
              }
              s.MatchCase(newPattern, guard, cse.rhs)
            }))

          case s.LetRec(fds, body) =>
            val funs = fds.map(fd => s.Inner(fd)(symbols))
            val newScope = scope withFunctions funs
            val newFuns = funs.map(fun => transformFunction(fun)(newScope in fun))
            val newBody = transformExpr(body)(newScope)
            t.LetRec(newFuns.map(_.toLocal), newBody)

          case _ => super.transform(e)
        }

        override def transform(pat: s.Pattern): t.Pattern = pat match {
          case s.ClassPattern(ob, ct, subs) =>

          case s.UnapplyPattern(ob, id, tps, subs) =>

          case _ => super.transform(pat)
        }

        override def transform(tpe: s.Type): t.Type = tpe match {
          case _ if !isSimple(tpe) => throw MissformedStainlessCode(tpe, "Unexpected non-simple type")
          case _ => super.transform(tpe)
        }
      }

      transformer.transform(e)
    }

    def transformFunction(fd: s.FunAbstraction)(implicit scope: Scope): t.FunAbstraction = {
      import s.TypeParameterWithBounds

      val tparamConds = fd.tparams.map { tpd =>
        val tp = tpd.tp
        val s.TypeBounds(lowerBound, upperBound) = tp.bounds

        val lower = if (lowerBound != s.NothingType) {
          subtypeOf(encodeType(lowerBound), getType(scope.tparams(tp)))
        } else {
          t.BooleanLiteral(true)
        }

        val upper = if (upperBound != s.AnyType) {
          subtypeOf(getType(scope.tparams(tp)), encodeType(upperBound))
        } else {
          t.BooleanLiteral(true)
        }

        t.and(lower, upper)
      }


      val paramConds = fd.params.map { vd =>
        if (isSimple(vd.tpe)) s.BooleanLiteral(true)
        else s.IsInstanceOf(vd.toVariable, vd.tpe)
      }

      val pre = s.andJoin(s.exprOps.preconditionOf(fd.fullBody).toSeq ++ paramConds) match {
        case s.BooleanLiteral(true) => None
        case cond => Some(cond)
      }

    }

    val symbolFuns = symbols.functions.values.map(s.Outer(_)(symbols)).toSeq
    val baseScope = Scope.empty withFunctions symbolFuns

    val functions: Seq[t.FunDef] = symbolFuns.map { fd =>
      // TODO: handle type parameter bounds for simpleFunctions
      if (baseScope.simple(fd.id)) identity.transform(fd.toFun)
      else transformFunction(fd)(baseScope).toFun
    }

    val adts: Seq[t.ADTDefinition] = symbols.adts.values.map { d =>

    }.toSeq

    t.NoSymbols
      .withFunctions(subtypeFunction +: functions)
      .withADTs(Seq(
        seqSort, consCons, nilCons, tpeSort,
        botCons, topCons, clsCons, adtCons, arrCons,
        setCons, bagCons, mapCons, tplCons, funCons
      ) ++ adts)
  }
}
