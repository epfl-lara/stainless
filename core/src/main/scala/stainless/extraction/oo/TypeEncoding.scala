/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

class TypeEncoding(override val s: Trees, override val t: Trees)
                  (using override val context: inox.Context)
  extends ExtractionPipeline
     with SimpleSorts
     with oo.CachingPhase
     with utils.SyntheticSorts { self =>

  import t._
  import t.dsl._

  /** A choice of a value of `res` that satisfies `pred` (Inox's DSL has no chooses). */
  private def choose(res: t.ValDef)(pred: t.Variable => t.Expr): t.Expr =
    t.Choose(res, pred(res.toVariable)).copiedFrom(res)

  override type FunctionResult = Seq[t.FunDef]
  protected def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  /* ====================================
   *             IDENTIFIERS
   * ==================================== */

  private class CachedID[T](builder: T => Identifier)
    extends utils.ConcurrentCached[T, Identifier](builder)

  private val refID = FreshIdentifier("Object")
  private def ref = T(refID)()

  private val (int,  intValue)  = (FreshIdentifier("Integer"),   FreshIdentifier("value"))
  private val (bool, boolValue) = (FreshIdentifier("Boolean"),   FreshIdentifier("value"))
  private val (char, charValue) = (FreshIdentifier("Character"), FreshIdentifier("value"))
  private val (real, realValue) = (FreshIdentifier("Real"),      FreshIdentifier("value"))
  private val (str,  strValue)  = (FreshIdentifier("String"),    FreshIdentifier("value"))
  private val (open, openValue) = (FreshIdentifier("Open"),      FreshIdentifier("value"))
  private val (arr,  arrValue)  = (FreshIdentifier("Array"),     FreshIdentifier("value"))
  private val (set,  setValue)  = (FreshIdentifier("Set"),       FreshIdentifier("value"))
  private val (bag,  bagValue)  = (FreshIdentifier("Bag"),       FreshIdentifier("value"))
  private val (map,  mapValue)  = (FreshIdentifier("Map"),       FreshIdentifier("value"))
  private val unit = FreshIdentifier("Unit")

  private val bv: ((Boolean, Int)) => Identifier = new CachedID[(Boolean, Int)]({
    case (signed, i) => FreshIdentifier((if (signed) "Signed" else "Unsigned") + "Bitvector" + i)
  })
  private val bvValue: ((Boolean, Int)) => Identifier =
    new CachedID[(Boolean, Int)](_ => FreshIdentifier("value"))

  private val fp: ((Int, Int)) => Identifier = new CachedID[(Int, Int)]({
    case (exponent, significand) => FreshIdentifier("FloatE" + exponent + "S" + significand)
  })
  private val fpValue: ((Int, Int)) => Identifier =
    new CachedID[(Int, Int)](_ => FreshIdentifier("value"))

  private val tpl: Int => Identifier = new CachedID[Int](i => FreshIdentifier("Tuple" + i))
  private val tplValue: Int => Identifier = new CachedID[Int](i => FreshIdentifier("value"))

  private val fun: Int => Identifier = new CachedID[Int](i => FreshIdentifier("Function" + i))
  private val funValue: Int => Identifier = new CachedID[Int](_ => FreshIdentifier("value"))

  private val adt: Identifier => Identifier = new CachedID[Identifier](_.freshen)
  private val adtValue: Identifier => Identifier = new CachedID[Identifier](_ => FreshIdentifier("value"))

  // The sorts of class hierarchies (see `TransformerContext.hierarchyOf`), by the root of the hierarchy, and the
  // constructors of `Object` that box their values
  private val hierarchyID = new CachedID[Identifier](_.freshen)
  private val hierarchyBox = new CachedID[Identifier](_.freshen)
  private val hierarchyValue = new CachedID[Identifier](_ => FreshIdentifier("value"))
  private def hierarchy(root: Identifier) = T(hierarchyID(root))()

  // Boxing of the values of type parameters that are not encoded, see `wrap` and `unwrap`
  private val boxID = FreshIdentifier("box")
  private val unboxID = FreshIdentifier("unbox")

  // First-order type codes, see `typeCode`
  private val codeID = FreshIdentifier("Type")
  private val isOfID = FreshIdentifier("isOf")
  private def code = T(codeID)()
  private val canonTypeParam: Int => s.TypeParameter =
    new utils.ConcurrentCached[Int, s.TypeParameter](i => s.TypeParameter(FreshIdentifier("T" + i), Seq()))
  private val canonVar: Int => Identifier = new CachedID[Int](i => FreshIdentifier("v" + i))


  /* ====================================
   *          OBJECT TESTING
   * ==================================== */

  private def isObject(tpe: s.Type)(using scope: Scope): Boolean = tpe match {
    case ct: s.ClassType => scope.context.hierarchyOf(ct.id).isEmpty
    case s.NothingType() | s.AnyType() => true
    case s.UnknownType(_) => true
    case s.TypeBounds(_, _, _) => true
    case tp: s.TypeParameter => scope.tparams contains tp
    case ta: s.TypeApply => ta.isAbstract(using scope.symbols)
    case _ => false
  }

  private def isSimple(tpe: s.Type)(using Scope): Boolean = !s.typeOps.exists(isObject)(tpe)

  /** The root of the hierarchy whose sort encodes the values of `tpe`, if any. */
  private def hierarchyOf(tpe: s.Type)(using scope: Scope): Option[Identifier] = tpe match {
    case ct: s.ClassType => scope.context.hierarchyOf(ct.id)
    case s.RefinementType(vd, _) => hierarchyOf(vd.tpe)
    case ta: s.TypeApply if !ta.isAbstract(using scope.symbols) => hierarchyOf(ta.resolve(using scope.symbols))
    case _ => None
  }


  private def simplify(lambda: t.Lambda): t.Expr = lambda match {
    case t.Lambda(Seq(vd), t.Application(f: t.Variable, Seq(v: t.Variable))) if vd.toVariable == v => f
    case _ => lambda
  }

  /* ====================================
   *      WRAPPING AND UNWRAPPING
   * ==================================== */

  private def getRefField(e: t.Expr, id: Identifier): t.Expr = e match {
    case v: t.Variable => t.Annotated(e.getField(id).copiedFrom(e), Seq(DropVCs)).copiedFrom(e)
    case _ => let(("x" :: ref.copiedFrom(e)).copiedFrom(e), e) { x =>
      t.Annotated(x.getField(id).copiedFrom(e), Seq(DropVCs)).copiedFrom(e)
    }.copiedFrom(e)
  }

  private def erased[T <: s.Type](tpe: T): T = {
    val s.NAryType(tps, recons) = tpe: @unchecked
    recons(tps.map(tp => s.AnyType().copiedFrom(tp))).copiedFrom(tpe).asInstanceOf[T]
  }

  private def erasedBy(tpe: s.Type)(using scope: Scope): s.Type = s.typeOps.postMap {
    case tp: s.TypeParameter if scope.tparams contains tp => Some(s.AnyType().copiedFrom(tp))
    case tb @ s.TypeBounds(s.NothingType(), s.AnyType(), _) => Some(s.AnyType().copiedFrom(tb))
    case _ => None
  } (tpe)

  private def wrap(e: t.Expr, tpe: s.Type)(using scope: Scope): t.Expr = (tpe match {
    case s.AnyType() => e
    case s.ClassType(id, tps) => scope.context.hierarchyOf(id) match {
      case Some(root) => C(hierarchyBox(root))(e)
      case None => e
    }
    // Values of the type parameters of sort invariants are boxed into uninterpreted objects, see `Scope.empty`
    case tp: s.TypeParameter if scope.boxed(tp) && !scope.tparams.contains(tp) =>
      t.FunctionInvocation(boxID, Seq(scope.transform(tp)), Seq(e))
    case tp: s.TypeParameter => e
    case s.ADTType(id, tps) => C(adt(id))(convert(e, tpe, erased(tpe)))
    case s.RefinementType(vd, pred) => wrap(e, vd.tpe)
    case (_: s.PiType | _: s.SigmaType) => wrap(e, erased(tpe))
    case s.FunctionType(from, _) => C(fun(from.size))(convert(e, tpe, erased(tpe)))
    case s.TupleType(tps) => C(tpl(tps.size))(convert(e, tpe, erased(tpe)))
    case (_: s.ArrayType) => C(arr)(convert(e, tpe, erased(tpe)))
    case (_: s.SetType) => C(set)(convert(e, tpe, erased(tpe)))
    case (_: s.BagType) => C(bag)(convert(e, tpe, erased(tpe)))
    case (_: s.MapType) => C(map)(convert(e, tpe, erased(tpe)))
    case s.BVType(signed, size) => C(bv(signed -> size))(e)
    case s.FPType(exponent, significand) => C(fp(exponent -> significand))(e)
    case s.IntegerType() => C(int)(e)
    case s.BooleanType() => C(bool)(e)
    case s.CharType() => C(char)(e)
    case s.RealType() => C(real)(e)
    case s.StringType() => C(str)(e)
    case s.UnitType() => let(("u" :: t.UnitType()).copiedFrom(e), e) { _ => t.ADT(unit, Seq(), Seq()).copiedFrom(e) }
  }).copiedFrom(e)

  /* ====================================
   *            TYPE CODES
   * ==================================== */

  /* Type parameters that are encoded (see `Scope.empty`) are passed as first-order type codes: values of
   * the synthetic sort `Type`, whose meaning is given by `isOf(x: Object, c: Type): Boolean`. This is a
   * defunctionalization of the type predicates `Object => Boolean`: each type that is passed as a type
   * argument gets a constructor of `Type`, whose fields are the codes of the type parameters and the values
   * of the variables that occur in it, and `isOf` interprets it with `instanceOf`.
   *
   * Type codes are not functions, so Inox has no lambdas to unroll against them.
   */

  /** A type up to the renaming of its type parameters and variables, to `T0`, `T1`, ... and `v0`, `v1`, ...
   *  in the order in which they occur.
   */
  private case class CodeKey(tpe: s.Type, typeParams: Int, vars: Seq[s.Variable])

  // The constructors of `Type`, which are the same across runs since cached functions refer to them
  private val codeCons: CodeKey => Identifier = new CachedID[CodeKey]({ key =>
    val name = key.tpe match {
      case s.ClassType(id, _) => id.name
      case s.ADTType(id, _) => id.name
      case _ => key.tpe.getClass.getSimpleName.stripSuffix("Type")
    }
    FreshIdentifier(name + "Type")
  })
  private val codeKeys = new java.util.concurrent.ConcurrentHashMap[Identifier, CodeKey]
  private val codeField: ((Identifier, Int)) => Identifier = new CachedID[(Identifier, Int)]({ case (_, i) =>
    FreshIdentifier("arg" + i)
  })

  /** The types `tpes` up to the renaming of their type parameters and free variables (see `CodeKey`): the
   *  renamed types, the type parameters and free variables in the order in which they occur, and their renamings.
   */
  private def canonical(tpes: Seq[s.Type]): (Seq[s.Type], Seq[s.TypeParameter], Seq[s.Variable], Seq[s.Variable]) = {
    val tps = scala.collection.mutable.ListBuffer.empty[s.TypeParameter]
    val vars = scala.collection.mutable.ListBuffer.empty[s.Variable]
    object collector extends s.ConcreteOOSelfTreeTraverser {
      override def traverse(tpe: s.Type): Unit = tpe match {
        case tp: s.TypeParameter => if (!tps.contains(tp)) tps += tp
        case _ => super.traverse(tpe)
      }
      override def traverse(e: s.Expr): Unit = e match {
        case v: s.Variable => if (!vars.contains(v)) vars += v; super.traverse(e)
        case _ => super.traverse(e)
      }
    }
    tpes.foreach(collector.traverse)
    val free = tpes.flatMap(s.typeOps.variablesOf).toSet
    val fvs = vars.filter(free).toSeq

    val tpSubst: Map[s.TypeParameter, s.Type] = tps.zipWithIndex.map { case (tp, i) => tp -> canonTypeParam(i) }.toMap
    val varSubst: Map[s.Variable, s.Variable] = fvs.zipWithIndex.map { case (v, i) =>
      v -> s.Variable(canonVar(i), s.typeOps.instantiateType(v.tpe, tpSubst), Seq())
    }.toMap
    (tpes.map(tpe => s.typeOps.replaceFromSymbols(varSubst, s.typeOps.instantiateType(tpe, tpSubst))),
      tps.toSeq, fvs, fvs.map(varSubst))
  }

  /** The code of type `tpe`, whose free type parameters are tested by codes in `scope`. */
  private def typeCode(tpe: s.Type)(using scope: Scope): t.Expr = tpe match {
    case tp: s.TypeParameter if scope.testers.contains(tp) => scope.testers(tp)
    // Type parameters that aren't encoded aren't tested (see `typeArgCode`)
    case tp: s.TypeParameter => anyCode
    case _ =>
      val (Seq(canon), tps, fvs, vars) = canonical(Seq(tpe)): @unchecked
      val key = CodeKey(canon, tps.size, vars)
      val id = codeCons(key)
      codeKeys.putIfAbsent(id, key)

      t.ADT(id, Seq(), tps.map(tp => typeCode(tp)) ++ fvs.map(v => scope.transform(v))).copiedFrom(tpe)
  }

  /** The code of `Any`, which any object satisfies. */
  private def anyCode(using scope: Scope): t.Expr = typeCode(s.AnyType())

  private def stripRefinements(tpe: t.Type): t.Type = t.typeOps.preMap {
    case t.RefinementType(vd, _) => Some(stripRefinements(vd.tpe))
    case _ => None
  } (tpe)

  // The parameters of `isOf`
  private val isOfX = FreshIdentifier("x")
  private val isOfC = FreshIdentifier("c")

  /** The constructor of the code `id`, and the case of `isOf` that interprets it. */
  private def codeDefinition(id: Identifier)(using context: TransformerContext): (t.ADTConstructor, t.MatchCase) = {
    val CodeKey(tpe, nTps, vars) = codeKeys.get(id)
    val tpVds = (0 until nTps).map(i => t.ValDef(FreshIdentifier("T" + i), code))
    val scope = context.emptyScope.testing((0 until nTps).map(canonTypeParam) zip tpVds.map(_.toVariable))
    // The variables keep their identifiers, so that the test refers to the binders of the case
    val varVds = vars.map(v => t.ValDef(v.id, stripRefinements(scope.transform(v.tpe))))
    val varMap = varVds.map(vd => vd.id -> vd.toVariable).toMap
    val test = t.exprOps.postMap {
      case v: t.Variable if varMap.contains(v.id) => Some(varMap(v.id))
      case _ => None
    } (instanceOf(t.Variable(isOfX, ref, Seq()), s.AnyType(), tpe)(using scope))

    val vds = tpVds ++ varVds
    val cons = new t.ADTConstructor(id, codeID, vds.zipWithIndex.map { case (vd, i) => t.ValDef(codeField(id -> i), vd.tpe) })
    val cse = t.MatchCase(t.ADTPattern(None, id, Seq(), vds.map(vd => t.WildcardPattern(Some(vd)))), None, test)
    (cons, cse)
  }

  /** The sort of the codes that `funs` and `sorts` use, and `isOf`. */
  private def codeDefinitions(funs: Iterable[t.FunDef], sorts: Iterable[t.ADTSort])
                             (using context: TransformerContext): (t.ADTSort, t.FunDef) = {
    def codesIn(traverse: t.ConcreteStainlessSelfTreeTraverser => Unit): Set[Identifier] = {
      var res = Set.empty[Identifier]
      val traverser = new t.ConcreteStainlessSelfTreeTraverser {
        override def traverse(e: t.Expr): Unit = e match {
          case t.ADT(id, _, _) if codeKeys.containsKey(id) => res += id; super.traverse(e)
          case _ => super.traverse(e)
        }
      }
      traverse(traverser)
      res
    }

    // `Any` always has a code, so that `Type` has a constructor
    val anyID = anyCode(using context.emptyScope) match { case t.ADT(id, _, _) => id case _ => sys.error("unreachable") }
    var todo = Set(anyID) ++ funs.flatMap(fd => codesIn(_.traverse(fd))) ++ sorts.flatMap(sort => codesIn(_.traverse(sort)))
    var definitions = Map.empty[Identifier, (t.ADTConstructor, t.MatchCase)]
    while (todo.nonEmpty) {
      val id = todo.head
      val definition = codeDefinition(id)
      definitions += id -> definition
      todo = todo.tail ++ (codesIn(_.traverse(definition._2.rhs)) -- definitions.keySet)
    }

    val sorted = definitions.toSeq.sortBy(_._1.globalId).map(_._2)
    val sort = new t.ADTSort(codeID, Seq(), sorted.map(_._1), Seq(t.Synthetic))
    val c = t.ValDef(isOfC, code)
    val isOf = new t.FunDef(isOfID, Seq(), Seq(t.ValDef(isOfX, ref), c), t.BooleanType(),
      t.MatchExpr(c.toVariable, sorted.map(_._2)), Seq(t.Synthetic, t.DropVCs))
    (sort, isOf)
  }

  /** Whether `e` is an instance of the encoded type parameter `tp`, whose code is `c`. */
  private def isOfCode(e: t.Expr, tp: s.Type, c: t.Expr)(using scope: Scope): t.Expr = {
    val test = t.FunctionInvocation(isOfID, Seq(), Seq(e, c)).copiedFrom(e)
    tp match {
      case tp: s.TypeParameter =>
        val s.TypeBounds(lo, hi, _) = tp.bounds: @unchecked
        val selfBounded = (s.typeOps.typeParamsOf(lo) ++ s.typeOps.typeParamsOf(hi)).contains(tp)
        if (selfBounded) test else {
          val upper = if (hi == s.AnyType()) test else t.and(test, instanceOf(e, s.AnyType(), hi)).copiedFrom(e)
          if (lo == s.NothingType()) upper else t.or(instanceOf(e, s.AnyType(), lo), upper).copiedFrom(e)
        }
      case _ => test
    }
  }

  /** The code passed for the type argument `tp` of a function whose type parameter is encoded.
   *
   *  The type parameters of sort invariants are not encoded (see `Scope.empty`): their values are boxed
   *  (see `wrap`), and any object may be such a box.
   */
  private def typeArgCode(tp: s.Type)(using scope: Scope): t.Expr = tp match {
    case tp: s.TypeParameter if scope.boxed(tp) && !scope.tparams.contains(tp) && !scope.testers.contains(tp) =>
      anyCode
    case _ => typeCode(tp)
  }

  private def unwrap(e: t.Expr, tpe: s.Type)(using scope: Scope): t.Expr = (tpe match {
    case s.AnyType() => e
    case s.ClassType(id, tps) => scope.context.hierarchyOf(id) match {
      case Some(root) => getRefField(e, hierarchyValue(root))
      case None => e
    }
    case tp: s.TypeParameter if scope.boxed(tp) && !scope.tparams.contains(tp) =>
      t.FunctionInvocation(unboxID, Seq(scope.transform(tp)), Seq(e))
    case tp: s.TypeParameter => e
    case s.ADTType(id, tps) => convert(getRefField(e, adtValue(id)), erased(tpe), tpe)
    case s.RefinementType(vd, pred) => unwrap(e, vd.tpe)
    case (_: s.PiType | _: s.SigmaType) => unwrap(e, erased(tpe))
    case s.FunctionType(from, _) => convert(getRefField(e, funValue(from.size)), erased(tpe), tpe)
    case s.TupleType(tps) => convert(getRefField(e, tplValue(tps.size)), erased(tpe), tpe)
    case (_: s.ArrayType) => convert(getRefField(e, arrValue), erased(tpe), tpe)
    case (_: s.SetType) => convert(getRefField(e, setValue), erased(tpe), tpe)
    case (_: s.BagType) => convert(getRefField(e, bagValue), erased(tpe), tpe)
    case (_: s.MapType) => convert(getRefField(e, mapValue), erased(tpe), tpe)
    case s.BVType(signed, size) => getRefField(e, bvValue(signed -> size))
    case s.FPType(exponent, significand) => getRefField(e, fpValue(exponent, significand))
    case s.IntegerType() => getRefField(e, intValue)
    case s.BooleanType() => getRefField(e, boolValue)
    case s.CharType() => getRefField(e, charValue)
    case s.RealType() => getRefField(e, realValue)
    case s.StringType() => getRefField(e, strValue)
    case s.UnitType() => let(("u" :: ref.copiedFrom(e)).copiedFrom(e), e) { _ => t.UnitLiteral().copiedFrom(e) }
  }).copiedFrom(e)


  /* ====================================
   *          TYPE CONVERSIONS
   * ==================================== */

  private val convertID = new CachedID[Identifier](id => FreshIdentifier("as" + id.name))

  /** Whether values of types `tpe` and `expected` have the same encoding, so that [[convert]] leaves them unchanged. */
  private def sameEncoding(tpe: s.Type, expected: s.Type)(using scope: Scope): Boolean = {
    val t1 = tpe.getType(using scope.symbols)
    val t2 = expected.getType(using scope.symbols)
    erasedBy(t1) == erasedBy(t2) || isObject(t1) && isObject(t2) ||
      hierarchyOf(t1).isDefined && hierarchyOf(t1) == hierarchyOf(t2)
  }

  private def convert(e: t.Expr, tpe: s.Type, expected: s.Type)(using scope: Scope): t.Expr = {
    val t1 = tpe.getType(using scope.symbols)
    val t2 = expected.getType(using scope.symbols)

    ((e, t1, t2) match {
      case _ if sameEncoding(t1, t2) => e

      // An unreachability assertion keeps its own description, such as that of a `throw`
      case (t.Assert(cond, err, t.NoTree(_)), s.NothingType(), t2) if !isObject(t2) =>
        t.Assert(cond, err, t.NoTree(scope.transform(t2)).copiedFrom(e)).copiedFrom(e)

      case (e, s.NothingType(), t2) if !isObject(t2) =>
        t.Error(scope.transform(t2), e match {
          case t.Error(_, descr) => descr
          case _ => s"Expression of type Nothing: ${e.toString}"
        })

      case (_, t1, t2) if isObject(t1) && !isObject(t2) => unwrap(e, t2)
      case (_, t1, t2) if !isObject(t1) && isObject(t2) => wrap(e, t1)

      case (_, t1, t2) if scope.converters `contains` (t1 -> t2) =>
        t.Application(scope.converters(t1 -> t2), Seq(e))

      case (_, t1, t2) if scope.converters `contains` t2 =>
        t.Application(scope.converters(t2), Seq(wrap(e, t1)))

      case (_, s.RefinementType(vd, pred), t2) =>
        convert(e, vd.tpe, t2)

      case (_, s.ADTType(id1, tps1), s.ADTType(id2, tps2)) if id1 == id2 && scope.converters.isEmpty && scope.context.isRegular(id1) =>
        sortConversion(e, id1, tps1, tps2)

      case (_, s.ADTType(id1, tps1), s.ADTType(id2, tps2)) if id1 == id2 =>
        t.FunctionInvocation(convertID(id1), (tps1 ++ tps2).map(tp => scope.transform(tp)),
          e +: (tps1 zip tps2 flatMap { case (tp1, tp2) => Seq(
            simplify(\(("x" :: scope.transform(tp1)).copiedFrom(tp1))(x => convert(x, tp1, tp2)).copiedFrom(tp1)),
            simplify(\(("x" :: scope.transform(tp2)).copiedFrom(tp2))(x => convert(x, tp2, tp1)).copiedFrom(tp2))
          )}
        ))

      case (t.Lambda(params, body), s.FunctionType(from1, to1), s.FunctionType(from2, to2)) =>
        val newParams = (params zip from2) map { case (vd, tpe) => vd.copy(tpe = scope.transform(tpe)).copiedFrom(vd) }
        val unifiedParams = newParams zip (from1 zip from2) map { case (vd, (tp1, tp2)) => convert(vd.toVariable, tp2, tp1) }
        val newBody = convert(t.exprOps.replaceFromSymbols((params.map(_.toVariable) zip unifiedParams).toMap, body), to1, to2)
        t.Lambda(newParams, newBody)

      case (_, s.FunctionType(from1, to1), s.FunctionType(from2, to2)) =>
        val newParams = from2.map(tp => t.ValDef.fresh("x", scope.transform(tp), true).copiedFrom(tp))
        val unifiedParams = newParams zip (from1 zip from2) map { case (vd, (tp1, tp2)) => convert(vd.toVariable, tp2, tp1) }
        t.Lambda(newParams, convert(t.Application(e, unifiedParams).copiedFrom(e), to1, to2))

      case (t.Tuple(es), s.TupleType(tps1), s.TupleType(tps2)) =>
        t.Tuple(es zip (tps1 zip tps2) map { case (e, (tp1, tp2)) => convert(e, tp1, tp2) })

      case (_, s.TupleType(tps1), s.TupleType(tps2)) =>
        t.Tuple((tps1 zip tps2).zipWithIndex map {
          case ((tp1, tp2), i) => convert(t.TupleSelect(e, i + 1).copiedFrom(e), tp1, tp2)
        })

      case (t.FiniteArray(elems, _), s.ArrayType(b1), s.ArrayType(b2)) =>
        t.FiniteArray(elems.map(e => convert(e, b1, b2)), scope.transform(b2))

      case (t.LargeArray(elems, dflt, size, base), s.ArrayType(b1), s.ArrayType(b2)) =>
        t.LargeArray(elems.map(p => p._1 -> convert(p._2, b1, b2)),
          convert(dflt, b1, b2), size, scope.transform(b2))

      case (t.ArrayUpdated(a, i, v), s.ArrayType(b1), s.ArrayType(b2)) =>
        t.ArrayUpdated(convert(a, tpe, expected), i, convert(v, b1, b2))

      case (_, s.ArrayType(b1), s.ArrayType(b2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
          res => forall(("i" :: t.Int32Type().copiedFrom(e)).copiedFrom(e)) {
            i => t.Equals(
              convert(t.ArraySelect(e, i).copiedFrom(e), b1, b2),
              t.ArraySelect(res, i).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case (t.FiniteSet(elems, _), s.SetType(b1), s.SetType(b2)) =>
        t.FiniteSet(elems.map(e => convert(e, b1, b2)), scope.transform(b2))

      case (t.SetAdd(set, elem), s.SetType(b1), s.SetType(b2)) =>
        t.SetAdd(convert(set, tpe, expected), convert(elem, b1, b2))

      case (t.SetIntersection(lhs, rhs), s.SetType(b1), s.SetType(b2)) =>
        t.SetIntersection(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.SetUnion(lhs, rhs), s.SetType(b1), s.SetType(b2)) =>
        t.SetUnion(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.SetDifference(lhs, rhs), s.SetType(b1), s.SetType(b2)) =>
        t.SetDifference(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (_, s.SetType(b1), s.SetType(b2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
          res => forall(("x" :: scope.transform(b1)).copiedFrom(e)) {
            x => t.Equals(
              t.ElementOfSet(x, e).copiedFrom(e),
              t.ElementOfSet(convert(x, b1, b2), res).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case (t.FiniteBag(elems, _), s.BagType(b1), s.BagType(b2)) =>
        t.FiniteBag(elems.map(p => p._1 -> convert(p._2, b1, b2)), scope.transform(b2))

      case (t.BagAdd(bag, elem), s.BagType(b1), s.BagType(b2)) =>
        t.BagAdd(convert(bag, tpe, expected), convert(elem, b1, b2))

      case (t.BagIntersection(lhs, rhs), s.BagType(b1), s.BagType(b2)) =>
        t.BagIntersection(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.BagUnion(lhs, rhs), s.BagType(b1), s.BagType(b2)) =>
        t.BagUnion(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.BagDifference(lhs, rhs), s.BagType(b1), s.BagType(b2)) =>
        t.BagDifference(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (_, s.BagType(b1), s.BagType(b2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
          res => forall(("x" :: scope.transform(b1)).copiedFrom(e)) {
            x => t.Equals(
              t.MultiplicityInBag(x, e).copiedFrom(e),
              t.MultiplicityInBag(convert(x, b1, b2), res).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case (t.FiniteMap(pairs, dflt, _, _), s.MapType(f1, t1), s.MapType(f2, t2)) =>
        t.FiniteMap(pairs.map(p => convert(p._1, f1, f2) -> convert(p._2, t1, t2)),
          convert(dflt, t1, t2), scope.transform(f2), scope.transform(t2))

      case (t.MapUpdated(m, k, v), s.MapType(f1, t1), s.MapType(f2, t2)) =>
        t.MapUpdated(convert(m, tpe, expected), convert(k, f1, f2), convert(v, t1, t2))

      case (_, s.MapType(f1, t1), s.MapType(f2, t2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
          res => forall(("x" :: scope.transform(f1)).copiedFrom(e)) {
            x => t.Equals(
              convert(t.MapApply(e, x).copiedFrom(e), t1, t2),
              t.MapApply(res, convert(x, f1, f2)).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case _ => t.Choose(
        t.ValDef.fresh("res", scope.transform(expected)).copiedFrom(e),
        t.BooleanLiteral(false).copiedFrom(e)
      )
    }).copiedFrom(e)
  }


  /* ====================================
   *          INSTANCE TESTS
   * ==================================== */

  private val instanceID = new CachedID[Identifier](id => FreshIdentifier("is" + id.name))

  def dealias(tp: s.Type)(using s.Symbols): s.Type = s.typeOps.preMap {
    case ta: s.TypeApply if !ta.isAbstract => Some(ta.resolve)
    case tp => None
  } (tp)

  private def instanceOf(e: t.Expr, in: s.Type, tpe: s.Type)(using scope: Scope): t.Expr = {
    ((dealias(in)(using scope.symbols), dealias(tpe)(using scope.symbols)) match {
      case (tp1, tp2) if (
        tp1 == tp2 &&
        !s.typeOps.typeParamsOf(tp2).exists { t2 =>
          (scope.testers `contains` t2) ||
          s.typeOps.typeParamsOf(tp1).exists { t1 =>
            scope.testers `contains` (t1 -> t2)
          }
        }
      ) => t.BooleanLiteral(true)

      case (tp1, tp2) if scope.testers `contains` (tp1 -> tp2) =>
        t.Application(scope.testers(tp1 -> tp2), Seq(e))

      case (tp1, tp2) if scope.testers `contains` tp2 =>
        isOfCode(wrap(e, tp1), tp2, scope.testers(tp2))

      case (_, s.AnyType()) => t.BooleanLiteral(true)
      case (_, s.NothingType()) => t.BooleanLiteral(false)

      case (_, s.UnknownType(_)) => t.BooleanLiteral(true)

      case (s.TypeBounds(_, hi, _), _) => instanceOf(e, hi, tpe)
      case (_, s.TypeBounds(_, hi, _)) => instanceOf(e, in, hi)

      case (s.RefinementType(vd, pred), _) => instanceOf(e, vd.tpe, tpe)

      case (_, s.RefinementType(vd, pred)) =>
        instanceOf(e, in, vd.tpe) &&
        t.Let(
          scope.transform(vd),
          convert(e, in, vd.tpe),
          scope.transform(pred, s.BooleanType().copiedFrom(pred))
        ).copiedFrom(e)

      case (_, s.ClassType(id, tps)) if scope.context.hierarchyOf(id).isDefined =>
        val root = scope.context.hierarchyOf(id).get
        def test(e: t.Expr) = t.FunctionInvocation(instanceID(id), Seq(), e +: tps.map(tp => typeCode(tp)))
        if (isObject(in)) {
          (e `is` hierarchyBox(root)).copiedFrom(e) && test(getRefField(e, hierarchyValue(root)))
        } else if (hierarchyOf(in) == Some(root)) {
          test(e)
        } else {
          t.BooleanLiteral(false)
        }

      case (_, s.ClassType(id, tps)) if isObject(in) =>
        t.FunctionInvocation(
          instanceID(id), Seq(),
          e +: tps.map(tp => typeCode(tp))
        )

      case (s.ADTType(id1, tps1), s.ADTType(id2, tps2)) if id1 == id2 && !scope.testers.hasPairs && scope.context.isRegular(id1) =>
        sortInstanceTest(e, id1, tps1, tps2)

      case (s.ADTType(id1, tps1), s.ADTType(id2, tps2)) if id1 == id2 =>
        t.FunctionInvocation(
          instanceID(id1), tps1 map (tp => scope.transform(tp)),
          e +: (tps1 zip tps2 map { case (tp1, tp2) =>
            simplify(\(("x" :: scope.transform(tp1)).copiedFrom(tp1)) { x =>
              instanceOf(x, tp1, tp2).copiedFrom(tp1)
            })
          })
        )

      case (_, s.ADTType(id, tps)) if isObject(in) =>
        (e `is` adt(id)).copiedFrom(e) &&
        instanceOf(getRefField(e, adtValue(id)), erased(tpe), tpe)

      case (ft1 @ (_: s.FunctionType | _: s.PiType), ft2 @ (_: s.FunctionType | _: s.PiType)) =>
        def extract(tpe: s.Type): (Seq[s.ValDef], s.Type) = tpe match {
          case s.FunctionType(from, to) => (from.map(tp => s.ValDef.fresh("x", tp, true).copiedFrom(tp)), to)
          case s.PiType(params, to) => (params, to)
        }

        val (nparams1, to1) = extract(ft1)
        val (nparams2, to2) = extract(ft2)

        val paramsCond = t.andJoin(nparams1 zip nparams2 map { case (vd1, vd2) =>
          instanceOf(scope.transform(vd2.toVariable), vd2.tpe, vd1.tpe)
        }).copiedFrom(e)

        val app = t.Application(e, nparams1 map (vd => scope.transform(vd.toVariable))).copiedFrom(e)
        val toCond = (nparams1 zip nparams2).foldRight(instanceOf(app, to1, to2)) { case ((vd1, vd2), e) =>
          val nvd1 = scope.transform(vd1)
          if (t.exprOps.variablesOf(e) contains nvd1.toVariable) {
            t.Let(nvd1, convert(scope.transform(vd2.toVariable), vd2.tpe, vd1.tpe), e).copiedFrom(e)
          } else {
            e
          }
        }

        t.Forall(nparams2.map(vd => scope.transform(vd)), t.Implies(paramsCond, toCond).copiedFrom(e))

      case (_, s.FunctionType(from, _)) if isObject(in) =>
        (e `is` fun(from.size)).copiedFrom(e) &&
        instanceOf(getRefField(e, funValue(from.size)), erased(tpe), tpe)

      case (_, s.PiType(params, _)) if isObject(in) =>
        (e `is` fun(params.size)).copiedFrom(e) &&
        instanceOf(getRefField(e, funValue(params.size)), erased(tpe), tpe)

      case (tt1 @ (_: s.TupleType | _: s.SigmaType), tt2 @ (_: s.TupleType | _: s.SigmaType)) =>
        def extract(tpe: s.Type): (Seq[s.ValDef], s.Type) = tpe match {
          case s.TupleType(from :+ to) => (from.map(tp => s.ValDef.fresh("x", tp, true).copiedFrom(tp)), to)
          case s.SigmaType(params, to) => (params, to)
        }

        val (nparams1, to1) = extract(tt1)
        val (nparams2, to2) = extract(tt2)

        val paramsCond = t.andJoin((nparams1 zip nparams2).zipWithIndex map { case ((vd1, vd2), i) =>
          instanceOf(t.TupleSelect(e, i + 1).copiedFrom(e), vd1.tpe, vd2.tpe)
        }).copiedFrom(e)

        val innerCond = instanceOf(t.TupleSelect(e, nparams1.size + 1).copiedFrom(e), to1, to2)

        val wrappedCond1 = nparams1.zipWithIndex.foldRight(innerCond) { case ((vd, i), body) =>
          val nvd = scope.transform(vd)
          if (t.exprOps.variablesOf(body) contains nvd.toVariable) {
            t.Let(nvd, t.TupleSelect(e, i + 1).copiedFrom(e), body).copiedFrom(body)
          } else {
            body
          }
        }

        val toCond = (nparams1 zip nparams2).zipWithIndex.foldRight(wrappedCond1) { case (((vd1, vd2), i), body) =>
          val nvd2 = scope.transform(vd2)
          if (t.exprOps.variablesOf(body) contains nvd2.toVariable) {
            t.Let(nvd2, convert(t.TupleSelect(e, i + 1).copiedFrom(e), vd1.tpe, vd2.tpe), body).copiedFrom(body)
          } else {
            body
          }
        }

        t.and(paramsCond, toCond)

      case (_, s.TupleType(tpes)) if isObject(in) =>
        (e `is` tpl(tpes.size)).copiedFrom(e) &&
        instanceOf(getRefField(e, tplValue(tpes.size)), erased(tpe), tpe)

      case (_, s.SigmaType(params, to)) =>
        (e `is` tpl(params.size + 1)).copiedFrom(e) &&
        instanceOf(getRefField(e, tplValue(params.size + 1)), erased(tpe), tpe)

      case (s.ArrayType(b1), s.ArrayType(b2)) =>
        forall(("i" :: Int32Type().copiedFrom(e)).copiedFrom(e)) { i =>
          ((
            (t.Int32Literal(0).copiedFrom(e) <= i).copiedFrom(e) &&
            (i < t.ArrayLength(e).copiedFrom(e)).copiedFrom(e)
          ) ==> (
            instanceOf(t.ArraySelect(e, i).copiedFrom(e), b1, b2)
          )).copiedFrom(e)
        }.copiedFrom(e)

      case (_, s.ArrayType(_)) if isObject(in) =>
        (e `is` arr).copiedFrom(e) &&
        instanceOf(getRefField(e, arrValue), erased(tpe), tpe)

      case (s.SetType(b1), s.SetType(b2)) =>
        forall(("x" :: scope.transform(b1)).copiedFrom(e)) { x =>
          (t.ElementOfSet(x, e).copiedFrom(e) ==> instanceOf(x, b1, b2)).copiedFrom(e)
        }.copiedFrom(e)

      case (_, s.SetType(_)) if isObject(in) =>
        (e `is` set).copiedFrom(e) &&
        instanceOf(getRefField(e, setValue), erased(tpe), tpe)

      case (s.BagType(b1), s.BagType(b2)) =>
        forall(("x" :: scope.transform(b1)).copiedFrom(e)) { x =>
          ((
            (t.MultiplicityInBag(x, e).copiedFrom(e) > IntegerLiteral(0).copiedFrom(e)).copiedFrom(e)
          ) ==> (
            instanceOf(x, b1, b2)
          )).copiedFrom(e)
        }.copiedFrom(e)

      case (_, s.BagType(_)) if isObject(in) =>
        (e `is` bag).copiedFrom(e) &&
        instanceOf(getRefField(e, bagValue), erased(tpe), tpe)

      case (s.MapType(f1, t1), s.MapType(f2, t2)) =>
        forall(("x" :: scope.transform(f1)).copiedFrom(e)) { x =>
          instanceOf(t.MapApply(e, x).copiedFrom(e), t1, t2)
        }

      case (_, s.MapType(_, _)) if isObject(in) =>
        (e `is` map).copiedFrom(e) &&
        instanceOf(getRefField(e, mapValue), erased(tpe), tpe)

      case (_, s.BVType(signed, size)) if isObject(in) => e `is` bv(signed -> size)
      case (_, s.IntegerType()) if isObject(in) => e `is` int
      case (_, s.BooleanType()) if isObject(in) => e `is` bool
      case (_, s.CharType()) if isObject(in) => e `is` char
      case (_, s.RealType()) if isObject(in) => e `is` real
      case (_, s.StringType()) if isObject(in) => e `is` str
      case (_, s.UnitType()) if isObject(in) => e `is` unit
      case _ => t.BooleanLiteral(false)
    }).copiedFrom(e)
  }


  /* ====================================
   *           CLASS INSTANCE
   * ==================================== */

  private def constructors(cd: s.ClassDef)(using s.Symbols): Seq[Identifier] =
    (cd +: cd.descendants).filterNot(_.flags contains s.IsAbstract).map(_.id)

  private def constructors(id: Identifier)(using symbols: s.Symbols): Seq[Identifier] =
    constructors(symbols.getClass(id))

  // The class instance function depends on the current class as well as its children on
  // which the `instanceOf` call well be recursively performed, so the cache key consists of
  // - the class definition
  // - the children class definitions
  private val classInstanceCache = new ExtractionCache[s.ClassDef, t.FunDef]({
    (cd, context) => ClassKey(cd) + SetKey(cd.children(using context.symbols).toSet)
  })

  private def classInstance(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.symbols
    import symbols.{given, _}
    val cd = symbols.getClass(id)
    classInstanceCache.cached(cd, context) {
      mkFunDef(instanceID(id), t.DropVCs, t.Synthetic)() { _ =>
        (("x" :: context.encodedClass(id)) +: cd.typeArgs.map(_.id.name :: code), BooleanType(), {
          case x +: tps =>
            given scope: Scope = context.emptyScope.testing(cd.typeArgs zip tps)
            if (cd.children.nonEmpty) {
              t.orJoin(
                cd.typed.children.map(ccd => instanceOf(x, cd.typed.toType, ccd.toType))
              )
            } else {
              (x `is` cd.id) &&
              t.andJoin(cd.fields.map(vd => instanceOf(t.ADTSelector(x, vd.id), vd.tpe, vd.tpe)))
            }
        })
      }
    }
  }


  /* ====================================
   *           CLASS UNAPPLY
   * ==================================== */

  private val unapplyID = new CachedID[Identifier](_.freshen)

  // The class unapply function depends on the current class and all its descendants
  // as it directly checks the dominated constructor set (no use of `instanceOf`).
  // The dependencies are therefore
  // - the class definition
  // - the descendant class definitions
  // - the synthetic OptionSort definitions
  private val classUnapplyCache = new ExtractionCache[s.ClassDef, t.FunDef]({ (cd, context) =>
    ClassKey(cd) + SetKey(cd.descendants(using context.symbols).toSet) + OptionSort.key(using context.symbols)
  })

  private def classUnapply(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.symbols
    import symbols.given
    val cd = symbols.getClass(id)
    classUnapplyCache.cached(cd, context) {
      import OptionSort._
      mkFunDef(unapplyID(cd.id), t.DropVCs, t.Synthetic, t.IsUnapply(isEmpty, get))() { _ =>
        val cons = constructors(cd)
        def condition(e: t.Expr): t.Expr = t.orJoin(cons.map(t.IsConstructor(e, _)))

        val scope = context.emptyScope.in(cd.id)
        val returnType = t.tupleTypeWrap(cd.fields.map(vd => scope.transform(vd.tpe)))
        (Seq("x" :: context.encodedClass(cd.id)), T(option)(returnType), { case Seq(x) =>
          if_ (condition(x)) {
            val r = t.tupleWrap(cd.fields.map(vd => t.ADTSelector(x, vd.id)))
            C(some)(returnType)(r)
          } else_ {
            C(none)(returnType)()
          }
        })
      }
    }
  }


  /* ====================================
   *         UNAPPLY FUNCTION
   * ==================================== */

  // The unapply function only depends on the synthetic OptionSort
  private val unapplyAnyCache = new ExtractionCache[s.Symbols, t.FunDef](
    (_, context) => OptionSort.key(using context.symbols)
  )

  private def unapplyAny(using context: TransformerContext): t.FunDef = unapplyAnyCache.cached(context.symbols, context) {
    import context.symbols.given
    import OptionSort.{value => _, _}
    mkFunDef(FreshIdentifier("InstanceOf"), t.DropVCs, t.Synthetic, t.IsUnapply(isEmpty, get))("A", "B") {
      case Seq(a, b) => (
        Seq("p" :: (a =>: t.BooleanType()), "t" :: (a =>: b), "x" :: a),
        T(option)(b), { case Seq(p, t, x) =>
          if_ (p(x)) {
            C(some)(b)(t(x))
          } else_ {
            C(none)(b)()
          }
        }
      )
    }
  }


  /* ====================================
   *           SORT INSTANCE
   * ==================================== */

  // The sort instance function depends only on the sort definition, so
  // we can use a simple cache here
  private val sortInstanceCache = new SimpleCache[s.ADTSort, t.FunDef]

  private def sortInstance(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.{symbols, emptyScope => scope}
    import symbols.given
    val sort = symbols.getSort(id)
    sortInstanceCache.cached(sort, context) {
      val in = sort.typeArgs.map(_.freshen)
      val tin = in.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])

      val x = "x" :: T(id)(tin*)
      val fs = tin map { i => i.id.name :: (i =>: t.BooleanType()) }

      val newScope = scope `testing` (in zip fs map { case (ti, vd) => (ti, ti) -> vd.toVariable })
      val fullBody = t.orJoin(sort.typed(in).constructors map { cons =>
        (x.toVariable `is` cons.id) &&
        t.andJoin(cons.fields.map(vd => instanceOf(x.toVariable.getField(vd.id), vd.tpe, vd.tpe)(using newScope)))
      })

      new t.FunDef(
        instanceID(id), tin.map(t.TypeParameterDef(_)), x +: fs, t.BooleanType(), fullBody,
        Seq(t.DropVCs, t.Synthetic)
      ).setPos(sort)
    }
  }


  /* ====================================
   *            SORT CONVERT
   * ==================================== */

  // The sort conversion function depends only on the sort definition, so
  // we can again use a simple cache here
  private val sortConvertCache = new SimpleCache[s.ADTSort, t.FunDef]

  private def sortConvert(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.{symbols, emptyScope => scope}
    import symbols.given
    val sort = symbols.getSort(id)
    sortConvertCache.cached(sort, context) {
      val (in, out) = (sort.typeArgs.map(_.freshen), sort.typeArgs.map(_.freshen))
      val tin = in.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])
      val tout = out.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])

      val x = "x" :: T(id)(tin*)
      val fs = tin zip tout map { case (i, o) => (i.id.name :: (i =>: o), i.id.name :: (o =>: i)) }

      val newScope = scope `converting` (in zip out zip fs flatMap {
        case ((ti, to), (vd1, vd2)) => Seq((ti, to) -> vd1.toVariable, (to, ti) -> vd2.toVariable)
      })

      val conversions = sort.typed(in).constructors zip sort.typed(out).constructors map { case (ci, co) =>
        (x.toVariable `is` ci.id, C(ci.id)(tout*)(ci.fields zip co.fields map { case (vi, vo) =>
          convert(x.toVariable.getField(vi.id), vi.tpe, vo.tpe)(using newScope)
        }*))
      }

      val fullBody = conversions.init.foldRight(conversions.last._2: Expr) {
        case ((cond, thenn), elze) => t.IfExpr(cond, thenn, elze)
      }

      new t.FunDef(
        convertID(id), (tin ++ tout).map(t.TypeParameterDef(_)), x +: fs.flatMap((vd1, vd2) => Seq(vd1, vd2)), T(id)(tout*), fullBody,
        Seq(t.DropVCs, t.Synthetic)
      ).setPos(sort)
    }
  }


  /* ====================================
   *    FIRST-ORDER SORT FUNCTIONS
   * ==================================== */

  /* A conversion between two instances of a sort, or a test of whether an instance of a sort is an instance
   * of another, is a call to a function that is specialized to these instances, up to the renaming of their
   * type parameters and variables. The conversions and tests of the type arguments are then inlined in its
   * body, instead of being passed as functions (see `sortConvert` and `sortInstance`), as type codes do for
   * the tests of encoded type parameters (see `typeCode`).
   *
   * In particular, the conversions of boxed type parameters (see `wrap`) are calls to `box` and `unbox`,
   * which would otherwise be passed as the lambdas `x => box(x)` and `x => unbox(x)`. Such lambdas are
   * equal to the uninterpreted functions of `box` and `unbox`, so a model could give them as their
   * interpretations, which would then be circular.
   *
   * There are finitely many such instances for regular sorts only, whose (transitive) fields only refer
   * to instances of sorts whose type arguments are type parameters of the sort (see `isRegular`). The
   * conversions and tests of instances of other sorts keep passing functions to `sortConvert` and
   * `sortInstance`, whose bodies then use these functions.
   */

  /** The conversion from `sort[from]` to `sort[to]` (or the test of whether a `sort[from]` is a `sort[to]`),
   *  whose type parameters are `T0`, `T1`, ... (of which `encoded` are encoded and `boxed` are boxed, see
   *  `Scope`, and `tested` are tested by type codes) and whose variables are `vars`.
   */
  private case class SortFunKey(test: Boolean, sort: Identifier, from: Seq[s.Type], to: Seq[s.Type], typeParams: Int,
                                encoded: Set[Int], boxed: Set[Int], tested: Seq[Int], vars: Seq[s.Variable])

  // The specialized functions, which are the same across runs since cached functions refer to them
  private val sortFun: SortFunKey => Identifier = new CachedID[SortFunKey](key =>
    FreshIdentifier((if (key.test) "is" else "as") + key.sort.name))
  private val sortFunKeys = new java.util.concurrent.ConcurrentHashMap[Identifier, SortFunKey]

  /** The conversion of `e` from `sort[tps1]` to `sort[tps2]`. */
  private def sortConversion(e: t.Expr, sort: Identifier, tps1: Seq[s.Type], tps2: Seq[s.Type])
                            (using scope: Scope): t.Expr = sortFunCall(false, e, sort, tps1, tps2)

  /** Whether `e` of type `sort[tps1]` is an instance of `sort[tps2]`. */
  private def sortInstanceTest(e: t.Expr, sort: Identifier, tps1: Seq[s.Type], tps2: Seq[s.Type])
                              (using scope: Scope): t.Expr = sortFunCall(true, e, sort, tps1, tps2)

  private def sortFunCall(test: Boolean, e: t.Expr, sort: Identifier, tps1: Seq[s.Type], tps2: Seq[s.Type])
                         (using scope: Scope): t.Expr = {
    val (canon, tps, fvs, vars) = canonical(tps1 ++ tps2)
    val (from, to) = canon.splitAt(tps1.size)
    val encoded = tps.indices.filter(i => scope.tparams(tps(i))).toSet
    val boxed = tps.indices.filter(i => scope.boxed(tps(i)) && !scope.tparams(tps(i))).toSet
    val tested = if (test) tps.indices.filter(i => scope.testers.contains(tps(i))) else Seq()
    val key = SortFunKey(test, sort, from, to, tps.size, encoded, boxed, tested, vars)
    val id = sortFun(key)
    sortFunKeys.putIfAbsent(id, key)

    // Encoded type parameters are objects, so the function doesn't depend on them but on their codes
    t.FunctionInvocation(id,
      tps.zipWithIndex.collect { case (tp, i) if !encoded(i) => scope.transform(tp) },
      (e +: tested.map(i => scope.testers(tps(i)))) ++ fvs.map(v => scope.transform(v))
    ).copiedFrom(e)
  }

  /** The specialized function `id`. */
  private def sortFunDefinition(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.symbols
    import symbols.given
    val SortFunKey(test, sortID, from, to, nTps, encoded, boxed, tested, vars) = sortFunKeys.get(id)
    val tps = (0 until nTps).map(canonTypeParam)
    val codeVds = tested.map(i => t.ValDef(FreshIdentifier("T" + i), code))
    // The type parameters and parameter of the function are those of the call, whose tested type parameters
    // are instantiated with their types in the scope of the call
    val carrier = new Scope(context.emptyScope.functions, encoded.map(tps), ExprMapping.empty, ExprMapping.empty, boxed.map(tps))
    given scope: Scope = carrier.testing(tested.map(tps) zip codeVds.map(_.toVariable))

    // The variables keep their identifiers, so that the body refers to the parameters
    val varVds = vars.map(v => t.ValDef(v.id, stripRefinements(scope.transform(v.tpe))))
    val varMap = varVds.map(vd => vd.id -> vd.toVariable).toMap
    def withParams(e: t.Expr): t.Expr = t.exprOps.postMap {
      case v: t.Variable if varMap.contains(v.id) => Some(varMap(v.id))
      case _ => None
    } (e)

    val sort = symbols.getSort(sortID)
    val x = ("x" :: carrier.transform(s.ADTType(sortID, from))).toVariable
    val constructors = sort.typed(from).constructors zip sort.typed(to).constructors

    val (returnType, fullBody) = if (test) {
      (t.BooleanType(), t.orJoin(constructors map { case (ci, co) =>
        (x `is` ci.id) && t.andJoin(ci.fields zip co.fields map { case (vi, vo) =>
          instanceOf(x.getField(vi.id), vi.tpe, vo.tpe)
        })
      }))
    } else {
      val conversions = constructors map { case (ci, co) =>
        (x `is` ci.id, C(ci.id)(to.map(scope.transform)*)(ci.fields zip co.fields map { case (vi, vo) =>
          convert(x.getField(vi.id), vi.tpe, vo.tpe)
        }*))
      }
      (scope.transform(s.ADTType(sortID, to)), conversions.init.foldRight(conversions.last._2: t.Expr) {
        case ((cond, thenn), elze) => t.IfExpr(cond, thenn, elze)
      })
    }

    new t.FunDef(
      id,
      tps.zipWithIndex.collect { case (tp, i) if !encoded(i) => t.TypeParameterDef(carrier.transform(tp).asInstanceOf[t.TypeParameter]) },
      (x.toVal +: codeVds) ++ varVds,
      returnType,
      withParams(fullBody),
      Seq(t.DropVCs, t.Synthetic)
    ).setPos(sort)
  }

  /** The specialized functions that `funs` call, transitively, apart from `known` ones. */
  private def sortFunDefinitions(funs: Iterable[t.FunDef], known: Set[Identifier])
                                (using context: TransformerContext): Seq[t.FunDef] = {
    def callsIn(fd: t.FunDef): Set[Identifier] = {
      var res = Set.empty[Identifier]
      val traverser = new t.ConcreteStainlessSelfTreeTraverser {
        override def traverse(e: t.Expr): Unit = e match {
          case t.FunctionInvocation(id, _, _) if sortFunKeys.containsKey(id) => res += id; super.traverse(e)
          case _ => super.traverse(e)
        }
      }
      traverser.traverse(fd)
      res
    }

    var todo = funs.flatMap(callsIn).toSet -- known
    var definitions = Map.empty[Identifier, t.FunDef]
    while (todo.nonEmpty) {
      val id = todo.head
      val fd = sortFunDefinition(id)
      definitions += id -> fd
      todo = todo.tail ++ (callsIn(fd) -- definitions.keySet -- known)
    }
    definitions.values.toSeq.sortBy(_.id.globalId)
  }


  /* =====================================
   *    TRANSFORMATION/ENCODING CONTEXT
   * ===================================== */

  /* Stores meta-data about functions useful during encoding.
   *
   * @param fun - function abstraction (FunDef or LocalFunDef)
   * @param outer - the scope in which the local function definition occurred
   * @param tparams - the type parameters that should be encoded to type codes
   */
  protected case class FunInfo(fun: s.FunAbstraction, tparams: Set[Int])

  protected class ExprMapping private(underlying: Map[(s.Type, Option[s.Type]), t.Expr]) {
    def contains(p: (s.Type, s.Type)): Boolean = underlying contains (p._1 -> Some(p._2))
    def contains(tpe: s.Type): Boolean = underlying contains (tpe -> None)
    def isEmpty: Boolean = underlying.isEmpty
    /** Whether some pairs of types are mapped, which only the generic sort functions do. */
    def hasPairs: Boolean = underlying.keys.exists(_._2.isDefined)

    def apply(p: (s.Type, s.Type)): t.Expr = underlying apply (p._1 -> Some(p._2))
    def apply(tpe: s.Type): t.Expr = underlying apply (tpe -> None)

    def ++(ps: Iterable[((s.Type, s.Type), t.Expr)]): ExprMapping =
      new ExprMapping(underlying ++ ps.map { case ((t1, t2), e) => ((t1, Some(t2)), e) })
    def ++(ps: Iterable[(s.Type, t.Expr)])(using DummyImplicit): ExprMapping =
      new ExprMapping(underlying ++ ps.map { case (tpe, e) => ((tpe, None), e) })

    override def toString = underlying.toString
  }

  protected object ExprMapping {
    def empty: ExprMapping = new ExprMapping(Map.empty)
  }

  protected class Scope private(
    override val s: self.s.type,
    override val t: self.t.type,
    val functions: Map[Identifier, FunInfo],
    val tparams: Set[s.TypeParameter],
    val testers: ExprMapping,
    val converters: ExprMapping,
    val boxed: Set[s.TypeParameter],
  )(using val context: TransformerContext, override val symbols: context.symbols.type) extends TransformerWithType {

    def this(functions: Map[Identifier, FunInfo],
             tparams: Set[self.s.TypeParameter],
             testers: ExprMapping,
             converters: ExprMapping,
             boxed: Set[self.s.TypeParameter])(using context: TransformerContext) =
      this(self.s, self.t, functions, tparams, testers, converters, boxed)(using context, context.symbols)

    protected given givenScope: this.type = this
    import symbols.{let => _, forall => _, _}

    def converting(ps: Iterable[((s.Type, s.Type), t.Expr)]): Scope =
      new Scope(functions, tparams, testers, converters ++ ps, boxed)

    def testing(ps: Iterable[((s.Type, s.Type), t.Expr)]): Scope =
      new Scope(functions, tparams, testers ++ ps, converters, boxed)
    def testing(ps: Iterable[(s.Type, t.Expr)])(using DummyImplicit): Scope =
      new Scope(functions, tparams, testers ++ ps, converters, boxed)
    def testing(p: (s.Type, t.Expr)): Scope =
      new Scope(functions, tparams, testers ++ Seq(p), converters, boxed)

    /** Box the values of type parameters `tps` when they reach encoded functions, see `wrap`. */
    def boxing(tps: Iterable[s.TypeParameter]): Scope =
      new Scope(functions, tparams, testers, converters, boxed ++ tps)

    override def transform(tp: s.Type): t.Type = tp match {
      case s.AnyType() => ref.copiedFrom(tp)
      case s.NothingType() =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(t.BooleanLiteral(false).copiedFrom(tp), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case s.UnknownType(_) => transform(s.AnyType().copiedFrom(tp))

      case ct: s.ClassType if context.hierarchyOf(ct.id).isDefined =>
        val root = context.hierarchyOf(ct.id).get
        val rootType = erased(s.ClassType(root, symbols.getClass(root).typeArgs).copiedFrom(tp))
        refinement(("x" :: hierarchy(root).copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(instanceOf(x, rootType, ct), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case ct: s.ClassType =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(instanceOf(x, s.AnyType().copiedFrom(tp), ct), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case s.TypeBounds(_, s.AnyType(), _) => ref.copiedFrom(tp)
      case s.TypeBounds(_, upperBound, _) =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(instanceOf(x, s.AnyType().copiedFrom(tp), upperBound), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case ta: s.TypeApply if ta.isAbstract =>
        transform(ta.bounds)

      case ta: s.TypeApply if !ta.isAbstract =>
        transform(ta.resolve)

      case tp: s.TypeParameter if testers `contains` tp =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(instanceOf(x, s.AnyType().copiedFrom(tp), tp), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case tp: s.TypeParameter if tparams contains tp => ref.copiedFrom(tp)

      case tp: s.TypeParameter => super.transform(tp.copy(
        flags = tp.flags.filterNot { case (_: s.Variance | _: s.Bounds) => true case _ => false }
      ).copiedFrom(tp))

      case _ => super.transform(tp)
    }

    def in(id: Identifier): Scope = {
      assert((functions contains id) || (classes contains id))
      val extraTParams = functions.get(id).map { case FunInfo(fun, tparams) =>
        fun.tparams.map(_.tp).zipWithIndex.collect { case (tp, i) if tparams(i) => tp }
      }.getOrElse(classes(id).typeArgs)
      new Scope(functions, tparams ++ extraTParams, testers, converters, boxed)
    }

    override def transform(e: s.Expr, inType: s.Type): t.Expr = e match {
      case s.ClassConstructor(ct, args) =>
        convert(t.ADT(ct.id, Seq(), (erased(ct).tcd.fields zip args).map {
          case (vd, arg) => convert(transform(arg), arg.getType, vd.tpe)
        }).copiedFrom(e), ct, inType)

      case s.ClassSelector(expr, id) =>
        val field = erased(expr.getType).asInstanceOf[s.ClassType].tcd.fields.find(_.id == id).get
        convert(t.ADTSelector(transform(expr), id).copiedFrom(e), field.getType, inType)

      case s.IsInstanceOf(expr, tpe) =>
        instanceOf(transform(expr), expr.getType, tpe).copiedFrom(e)

      case s.AsInstanceOf(expr, tpe) =>
        val vd = t.ValDef.fresh("x", transform(expr.getType)).copiedFrom(e)
        val cond = instanceOf(vd.toVariable, expr.getType, tpe).copiedFrom(e)
        if (cond == BooleanLiteral(true))
          convert(transform(expr), expr.getType, inType)
        else
          convert(t.Let(vd, transform(expr), t.Assert(
            cond,
            Some("Cast error"),
            convert(vd.toVariable, expr.getType, tpe).copiedFrom(e)
          ).copiedFrom(e)).copiedFrom(e), tpe, inType)

      case fi @ s.FunctionInvocation(id, tps, args) =>
        val funScope = this `in` id
        val FunInfo(fun, tparams) = functions(id)
        val tpSubst = (fun.tparams.map(_.tp) zip tps).zipWithIndex.map {
          case ((tp, tpe), i) => tp -> (if (tparams(i)) tp else tpe)
        }.toMap

        convert(t.FunctionInvocation(id,
          tps.zipWithIndex.collect { case (tp, i) if !tparams(i) => transform(tp) },
          tps.zipWithIndex.collect { case (tp, i) if tparams(i) =>
            typeArgCode(tp)
          } ++ (fun.params zip args).map { case (vd, arg) =>
            convert(transform(arg), arg.getType, s.typeOps.instantiateType(vd.tpe, tpSubst))(using funScope)
          }).copiedFrom(e), s.typeOps.instantiateType(fun.returnType.getType, tpSubst), inType)(using funScope)

      case app @ s.ApplyLetRec(id, tparams, tpe, tps, args) =>
        val funScope = this `in` id
        val FunInfo(fun, ctparams) = functions(id)
        val tpSubst = (fun.tparams.map(_.tp) zip tps).zipWithIndex.map {
          case ((tp, tpe), i) => tp -> (if (ctparams(i)) tp else tpe)
        }.toMap

        val nparams = tparams.zipWithIndex.collect { case (tp, i) if ctparams(i) => code.copiedFrom(tp) }

        convert(t.ApplyLetRec(
          id,
          tparams.zipWithIndex.collect { case (tp, i) if !ctparams(i) => transform(tp).asInstanceOf[t.TypeParameter] },
          t.FunctionType(nparams ++ tpe.from.map(funScope.transform), funScope.transform(tpe.to)).copiedFrom(tpe),
          tps.zipWithIndex.collect { case (tp, i) if !ctparams(i) => transform(tp) },
          tps.zipWithIndex.collect {  case (tp, i) if ctparams(i) =>
            typeArgCode(tp)
          } ++ (fun.params zip args).map { case (vd, arg) =>
            convert(transform(arg), arg.getType, s.typeOps.instantiateType(vd.tpe, tpSubst))(using funScope)
          }).copiedFrom(app), s.typeOps.instantiateType(fun.returnType.getType, tpSubst), inType)(using funScope)

      case s.LetRec(fds, body) =>
        val funs = fds.map(fd => s.Inner(fd))
        val newFuns = funs.map(transform(_))
        val newBody = transform(body, inType)
        t.LetRec(newFuns.map(_.toLocal), newBody).copiedFrom(e)

      // `TransformerWithType` types the patterns of a match against the upper bound of a type parameter, but the
      // scrutinee of an encoded type parameter is an `Object`: typing them against the type parameter itself makes
      // them unwrap it, as `isInstanceOf` does.
      case s.MatchExpr(scrut, cses) if isObject(scrut.getType) && !isObject(widen(scrut.getType)) =>
        t.MatchExpr(
          transform(scrut),
          cses.map { case cse @ s.MatchCase(pat, guard, rhs) =>
            t.MatchCase(
              transform(pat, scrut.getType),
              guard.map(transform(_, s.BooleanType())),
              transform(rhs, inType)
            ).copiedFrom(cse)
          }
        ).copiedFrom(e)

      // `TransformerWithType` compares values at the widened upper bound of their types, which is `Any` for type
      // parameters, but values of a boxed type parameter can be compared without boxing them
      case s.Equals(lhs, rhs) if (lhs.getType, rhs.getType) match {
        case (tp: s.TypeParameter, tp2) => tp == tp2 && boxed(tp) && !tparams(tp)
        case _ => false
      } => t.Equals(transform(lhs, lhs.getType), transform(rhs, rhs.getType)).copiedFrom(e)

      // push conversions down into branches/leaves
      case (_: s.IfExpr | _: s.MatchExpr | _: s.Let) => super.transform(e, inType)

      // and below specifications, which must stay at the top of function bodies
      case (_: s.Require | _: s.Decreases) => super.transform(e, inType)

      // the postcondition then receives the converted result, so convert it back to the type of its parameter
      case s.Ensuring(body, pred @ s.Lambda(Seq(vd), post)) if !sameEncoding(inType, vd.getType) =>
        val res = t.ValDef(vd.id.freshen, transform(inType)).copiedFrom(vd)
        t.Ensuring(
          transform(body, inType),
          t.Lambda(Seq(res), t.Let(
            transform(vd),
            convert(res.toVariable, inType, vd.getType),
            transform(post, s.BooleanType())
          ).copiedFrom(post)).copiedFrom(pred)
        ).copiedFrom(e)

      case _: s.Ensuring => super.transform(e, inType)

      case e if isObject(e.getType) != isObject(inType) =>
        convert(transform(e), e.getType, inType)

      case _ =>
        super.transform(e, inType)
    }

    private def instanceOfPattern(inner: t.Pattern, in: s.Type, tpe: s.Type): t.Pattern =
      if (isSubtypeOf(in, tpe) && isObject(tpe) == isObject(in)) {
        inner
      } else {
        t.UnapplyPattern(
          None, Seq(
            \(("x" :: transform(in)).copiedFrom(inner))(x => instanceOf(x, in, tpe)).copiedFrom(inner),
            \(("x" :: transform(in)).copiedFrom(inner))(x => convert(x, in, tpe)).copiedFrom(inner)
          ), unapplyAny.id, Seq(transform(in), transform(tpe)), Seq(inner)
        ).copiedFrom(inner)
      }

    private def withRefine(vd: s.ValDef)(body: => t.Pattern): t.Pattern =
      vd.tpe match {
        case s.RefinementType(vd1, pred) => 
          withRefine(vd1) {
            t.RefinementPattern(body, t.Lambda(Seq(transform(vd1)), transform(pred)))
          }
        case _ => body
      }

    override def transform(pat: s.Pattern, tpe: s.Type): t.Pattern = pat match {
      case s.WildcardPattern(None) => t.WildcardPattern(None).copiedFrom(pat)
      case s.WildcardPattern(Some(vd)) if isObject(vd.tpe) && isObject(tpe) =>
        t.WildcardPattern(Some(transform(vd))).copiedFrom(pat)
      case s.WildcardPattern(Some(vd)) =>
        withRefine(vd) {
          instanceOfPattern(t.WildcardPattern(Some(transform(vd))).copiedFrom(pat), tpe, vd.getType)
        }.copiedFrom(pat)

      case s.InstanceOfPattern(ob, tp) =>
        instanceOfPattern(t.WildcardPattern(ob map transform).copiedFrom(pat), tpe, tp)

      case s.ClassPattern(ob, ct, subs) => tpe match {
        case cti: s.ClassType if (
          (cti +: cti.tcd.descendants.map(_.toType)).exists(isSubtypeOf(_, ct)) &&
          (!(ct.tcd.cd.flags contains s.IsAbstract) && ct.tcd.children.isEmpty)
        ) =>
          val erasedTps = ct.tps.map(tp => if (isObject(tp)) tp else s.AnyType().copiedFrom(tp))
          val semiErased = ct.copy(tps = erasedTps).copiedFrom(ct)
          t.ADTPattern(
            ob map transform, ct.id, Seq(),
            subs zip semiErased.tcd.fields map { case (sub, vd) => transform(sub, vd.getType) }
          ).copiedFrom(pat)

        case _ =>
          instanceOfPattern(t.UnapplyPattern(
            ob map transform, Seq(), unapplyID(ct.id), Seq(),
            subs zip erased(ct).tcd.fields map { case (sub, vd) => transform(sub, vd.getType) }
          ).copiedFrom(pat), tpe, ct)
      }

      case s.ADTPattern(ob, id, tps, subs) =>
        val sort = s.ADTType(getConstructor(id).sort, tps).copiedFrom(tpe)
        // Patterns can't test the refinements of type arguments, which are erased at runtime: the
        // instance check is on the unrefined sort (the type of the scrutinee has no refinements either,
        // see `TransformerWithType`)
        instanceOfPattern(super.transform(pat, sort), tpe, sort.getType)

      case s.TuplePattern(None, subs) => tpe match {
        case s.TupleType(tps) if subs.size == tps.size => super.transform(pat, tpe)
        case _ =>
          val tt = s.TupleType(subs.map(sub => s.AnyType().copiedFrom(sub))).copiedFrom(pat)
          instanceOfPattern(super.transform(pat, tt), tpe, tt)
      }

      case s.TuplePattern(Some(vd), subs) =>
        withRefine(vd) {
          instanceOfPattern(super.transform(pat, vd.getType), tpe, vd.getType)
        }.copiedFrom(pat)

      case s.AlternativePattern(None, subs) =>
        t.AlternativePattern(None, subs.map(transform)).copiedFrom(pat)

      case s.AlternativePattern(Some(vd), subs) =>
        withRefine(vd) {
          instanceOfPattern(t.AlternativePattern(Some(transform(vd)), subs.map(transform)).copiedFrom(pat), tpe, vd.getType)
        }.copiedFrom(pat)

      case s.RefinementPattern(pat, pred) =>
        t.RefinementPattern(transform(pat, tpe.getType), transform(pred).asInstanceOf[t.Lambda]).copiedFrom(pat)

      case up @ s.UnapplyPattern(ob, recs, id, tps, subs) =>
        val funScope = this `in` id
        val FunInfo(fun, tparams) = functions(id)
        val tpSubst = (fun.tparams.map(_.tp) zip tps).zipWithIndex.map {
          case ((tp, tpe), i) => tp -> (if (tparams(i)) tp else tpe)
        }.toMap

        t.UnapplyPattern(
          ob map transform,
          tps.zipWithIndex.flatMap { case (tp, i) =>
            if (tparams(i)) Seq(
              typeArgCode(tp),
              \(("x" :: ref).copiedFrom(tp))(x => unwrap(x, tp)).copiedFrom(tp)
            ) else Seq.empty[t.Expr]
          } ++ (recs zip fun.params.init).map {
            case (r, vd) => convert(transform(r), r.getType, s.typeOps.instantiateType(vd.tpe, tpSubst))(using funScope)
          }, id, tps.zipWithIndex.collect { case (tp, i) if !tparams(i) => transform(tp) },
          subs zip up.subTypes(tpe) map (p => transform(p._1, p._2))
        ).copiedFrom(pat)

      case s.LiteralPattern(ob, lit) =>
        instanceOfPattern(super.transform(pat, lit.getType), tpe, lit.getType)
    }

    override def transform(fd: s.FunDef): t.FunDef = transform(s.Outer(fd)).toFun

    def transform(fd: s.FunAbstraction): t.FunAbstraction = {
      val FunInfo(_, tparams) = functions(fd.id)

      val ntparams = fd.tparams.zipWithIndex.collect { case (tpd, i) if !tparams(i) => transform(tpd) }

      val (scope, tparamParams) = fd.tparams.map(_.tp).zipWithIndex
        .collect { case (tp, i) if tparams(i) => tp }
        .foldLeft((
          // Sort invariants keep the type parameters of their sort (see `Scope.empty`), and box their values
          if (fd.flags contains s.IsInvariant) (this `in` fd.id).boxing(fd.tparams.map(_.tp)) else (this `in` fd.id),
          Seq[t.ValDef]())) {
          case ((scope, vds), tp) =>
            // The bounds of `tp` are part of its test, see `isOfCode`
            val vd = t.ValDef(tp.id.freshen, code.copiedFrom(tp)).copiedFrom(tp)
            (scope.testing(tp -> vd.toVariable), vds :+ vd)
        }

      fd.to(t)(
        fd.id,
        ntparams,
        tparamParams ++ fd.params.map(scope.transform(_)),
        scope.transform(fd.returnType),
        scope.transform(fd.fullBody, fd.returnType.getType),
        fd.flags map scope.transform
      )
    }
  }

  private object Scope {
    def empty(using context: TransformerContext): Scope = {
      import context.symbols
      import symbols.{given, _}

      def computeInfo(fun: s.FunAbstraction)(infos: Map[Identifier, FunInfo]): FunInfo = {
        val tparams: Seq[s.TypeParameter] = fun.tparams.map(_.tp)
        var simple: Set[s.TypeParameter] = tparams.toSet

        class Traverser(override val s: self.s.type, override val t: self.s.type)
                       (using override val symbols: context.symbols.type)
          extends TransformerWithType {

          override def transform(pat: s.Pattern, in: s.Type): t.Pattern = pat match {
            case s.InstanceOfPattern(_, tpe) if leastUpperBound(tpe, in) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(in.getType)
              simple --= s.typeOps.typeParamsOf(tpe.getType)
              super.transform(pat, in)

            case s.ClassPattern(_, ct, _) =>
              if (leastUpperBound(ct, in) == s.AnyType()) {
                simple --= s.typeOps.typeParamsOf(in.getType)
              }
              simple --= s.typeOps.typeParamsOf(ct.getType)
              super.transform(pat, in)

            case s.ADTPattern(ob, id, tps, subs) =>
              if (leastUpperBound(in, s.ADTType(getConstructor(id).sort, tps)) == s.AnyType()) {
                simple --= s.typeOps.typeParamsOf(in.getType)
                tps.foreach(tp => simple --= s.typeOps.typeParamsOf(tp.getType))
              }
              super.transform(pat, in)

            case s.TuplePattern(ob, subs) => widen(in.getType) match {
              case s.TupleType(tps) if tps.size == subs.size =>
                super.transform(pat, in)
              case _ =>
                simple --= s.typeOps.typeParamsOf(in.getType)
                super.transform(pat, in)
            }

            case s.AlternativePattern(ob, subs) =>
              simple --= s.typeOps.typeParamsOf(in.getType)
              super.transform(pat, in)

            case s.RefinementPattern(pat, pred) =>
              simple --= s.typeOps.typeParamsOf(in.getType)
              super.transform(pat, in)

            case up @ s.UnapplyPattern(ob, recs, id, tps, subs) =>
              val tparams = infos(id).tparams
              simple --= tps.zipWithIndex.flatMap { case (tp, i) =>
                if (tparams(i)) s.typeOps.typeParamsOf(tp.getType)
                else Set.empty[s.TypeParameter]
              }
              super.transform(pat, in)

            case s.LiteralPattern(_, lit) if leastUpperBound(lit.getType, in) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(in.getType)
              super.transform(pat, in)

            case _ => super.transform(pat, in)
          }

          override def transform(e: s.Expr, tpe: s.Type): t.Expr = e match {
            case s.IsInstanceOf(expr, tp) if leastUpperBound(expr.getType, tp) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(expr.getType)
              simple --= s.typeOps.typeParamsOf(tp.getType)
              super.transform(e, tpe)

            case s.AsInstanceOf(expr, tp) if leastUpperBound(expr.getType, tp) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(expr.getType)
              simple --= s.typeOps.typeParamsOf(tp.getType)
              super.transform(e, tpe)

            // A value of a generic ADT type used as `Any` is converted to `Object`, along with the values of
            // its type parameters, which therefore can't be simple
            case _ if tpe == s.AnyType() && (e.getType match { case s.ADTType(_, tps) => tps.nonEmpty case _ => false }) =>
              simple --= s.typeOps.typeParamsOf(e.getType)
              transform(e, e.getType)

            case s.FunInvocation(id, tps, args, _) =>
              val tparams = infos(id).tparams
              simple --= tps.zipWithIndex.flatMap { case (tp, i) =>
                if (tparams(i)) s.typeOps.typeParamsOf(tp.getType)
                else Set.empty[s.TypeParameter]
              }
              super.transform(e, tpe)

            case _ => super.transform(e, tpe)
          }

          override def transform(tpe: s.Type): t.Type = tpe match {
            case s.ClassType(id, tps) =>
              simple --= tps.flatMap(tp => s.typeOps.typeParamsOf(tp))
              super.transform(tpe)

            case tp: s.TypeParameter if simple(tp) =>
              val bounds = tp.flags.collect {
                case s.Bounds(lo, hi) => Seq(lo, hi)
              }.flatten.toSet

              val boundParams = tparams.filter(bounds.flatMap(s.typeOps.typeParamsOf))

              if (bounds.nonEmpty) {
                simple -= tp
                boundParams foreach { param =>
                  simple -= param
                }
              }

              super.transform(tpe)

            case _ => super.transform(tpe)
          }
        }

        val traverser = new Traverser(self.s, self.s)(using context.symbols)

        fun.tparams map (traverser.transform(_))
        fun.params map (traverser.transform(_))
        traverser.transform(fun.returnType)
        traverser.transform(fun.fullBody, fun.returnType.getType)
        fun.flags map (traverser.transform(_))

        // Sort invariants must keep the type parameters of their sort. When they call functions whose type
        // parameters are encoded, the values of their type parameters are boxed (see `wrap`).
        if (fun.flags contains s.IsInvariant) simple = tparams.toSet

        val nonSimpleParamsIndices = tparams.zipWithIndex.collect {
          case (tp, i) if !simple(tp) => i
        }.toSet

        FunInfo(fun, nonSimpleParamsIndices)
      }

      val functions = context.symbols.functions.values.toSeq.flatMap { fd =>
        val inners = s.exprOps.collect {
          case s.LetRec(fds, _) => fds.toSet
          case _ => Set.empty[s.LocalFunDef]
        } (fd.fullBody)

        Seq(s.Outer(fd)) ++ inners.map(s.Inner(_))
      }

      val infos = inox.utils.fixpoint { (infos: Map[Identifier, FunInfo]) =>
        infos.map { case (id, info) => id -> computeInfo(info.fun)(infos) }
      } (functions.map(fun => fun.id -> FunInfo(fun, Set.empty)).toMap)

      new Scope(infos, Set.empty, ExprMapping.empty, ExprMapping.empty, Set.empty)
    }
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) {
    import symbols.{given, _}
    given emptyScope: Scope = Scope.empty(using this)

    private val regularSorts = scala.collection.concurrent.TrieMap.empty[Identifier, Boolean]

    /** Whether the instances of sort `id` that its values contain are finitely many (see `sortFunCall`). */
    def isRegular(id: Identifier): Boolean = regularSorts.getOrElseUpdate(id, {
      var seen = Set.empty[s.ADTType]
      var todo = List(s.ADTType(id, symbols.getSort(id).typeArgs))
      while (todo.nonEmpty && seen.size <= 100) {
        val tpe = todo.head
        todo = todo.tail
        if (!seen(tpe)) {
          seen += tpe
          todo ++= tpe.getSort.constructors.flatMap(_.fields).flatMap(vd => s.typeOps.collect[s.ADTType] {
            case at: s.ADTType => Set(at)
            case _ => Set.empty
          } (vd.tpe))
        }
      }
      todo.isEmpty
    })

    private val (tplSizes, funSizes, bvSizes, fpSizes) = {
      var tplSizes: Set[Int] = Set.empty
      var funSizes: Set[Int] = Set.empty
      var bvSizes: Set[(Boolean, Int)] = Set.empty
      var fpSizes: Set[(Int, Int)] = Set.empty

      object traverser extends s.ConcreteOOSelfTreeTraverser {
        override def traverse(pat: s.Pattern): Unit = pat match {
          case s.TuplePattern(_, subs) => tplSizes += subs.size; super.traverse(pat)
          case _ => super.traverse(pat)
        }

        override def traverse(tpe: s.Type): Unit = tpe match {
          case s.TupleType(tps) => tplSizes += tps.size; super.traverse(tpe)
          case s.SigmaType(params, _) => tplSizes += params.size + 1; super.traverse(tpe)
          case s.FunctionType(from, _) => funSizes += from.size; super.traverse(tpe)
          case s.PiType(params, _) => funSizes += params.size; super.traverse(tpe)
          case s.BVType(signed, size) => bvSizes += (signed -> size); super.traverse(tpe)
          case s.FPType(exponent, significand) => fpSizes += (exponent -> significand); super.traverse(tpe)
          case _ => super.traverse(tpe)
        }

        override def traverse(expr: s.Expr): Unit = expr match {
          case s.Tuple(es) => tplSizes += es.size; super.traverse(expr)
          case s.Lambda(params, _) => funSizes += params.size; super.traverse(expr)
          case s.BVLiteral(signed, _, size) => bvSizes += (signed -> size); super.traverse(expr)
          case s.FPLiteral(exponent, significand, _) => fpSizes += (exponent -> significand); super.traverse(expr)
          case s.ArrayLength(_) => bvSizes += (true -> 32); super.traverse(expr)
          case _ => super.traverse(expr)
        }
      }

      symbols.functions.values.foreach(traverser.traverse)

      (tplSizes, funSizes, bvSizes, fpSizes)
    }

    private val hierarchies = scala.collection.concurrent.TrieMap.empty[Identifier, Option[Identifier]]

    /** The root of the hierarchy of class `id`, when the values of the hierarchy are encoded by a sort of
     *  their own instead of `Object`: the root is sealed, every class of the hierarchy has it as only root,
     *  and the classes with children are sealed. Conversions to `Any` box these values into `Object`. */
    def hierarchyOf(id: Identifier): Option[Identifier] = hierarchies.getOrElseUpdate(id, {
      val cd = symbols.getClass(id)
      def roots(cd: s.ClassDef): Seq[Identifier] = (cd +: cd.ancestors.map(_.cd)).filter(_.parents.isEmpty).map(_.id).distinct
      roots(cd) match {
        case Seq(root) =>
          val rcd = symbols.getClass(root)
          val classes = rcd +: rcd.descendants
          val eligible = (rcd.flags contains s.IsSealed) && (rcd.flags contains s.IsAbstract) &&
            classes.forall { cd =>
              roots(cd) == Seq(root) && cd.typeMembers.isEmpty &&
              (cd.children.isEmpty || (cd.flags contains s.IsSealed)) &&
              !(cd.flags contains s.IsExtensible)
            }
          if (eligible) Some(root) else None
        case _ => None
      }
    })

    /** The type of the encoded values of class `id`, without the refinement of their type test. */
    def encodedClass(id: Identifier): t.Type = hierarchyOf(id) match {
      case Some(root) => hierarchy(root)
      case None => ref
    }

    private def constructor(cd: s.ClassDef, sort: Identifier): t.ADTConstructor = {
      val anys = cd.typeArgs.map(tp => s.AnyType().copiedFrom(tp))
      // Fields whose types mention type parameters of the class aren't refined by their type tests: the type
      // test of the class already covers them, and refinements of the fields of a sort are unrolled for every
      // value of the sort. The type test of the class skips the other fields, which keep their refinements.
      val fields = (cd.fields zip cd.typed(anys).fields.map(emptyScope.transform)).map { case (field, vd) =>
        vd.tpe match {
          case t.RefinementType(v, t.Annotated(_, Seq(t.DropConjunct)))
              if s.typeOps.typeParamsOf(field.tpe).exists(cd.typeArgs.contains) =>
            vd.copy(tpe = v.tpe).copiedFrom(vd)
          case _ => vd
        }
      }
      new t.ADTConstructor(cd.id, sort, fields).copiedFrom(cd)
    }

    private val concreteClasses = symbols.classes.values.toSeq.filterNot(_.flags contains s.IsAbstract)

    private val hierarchyRoots: Seq[Identifier] = concreteClasses.flatMap(cd => hierarchyOf(cd.id)).distinct

    val hierarchySorts: Seq[t.ADTSort] = hierarchyRoots.map { root =>
      val rcd = symbols.getClass(root)
      new t.ADTSort(hierarchyID(root), Seq(),
        concreteClasses.filter(cd => hierarchyOf(cd.id) == Some(root)).map(constructor(_, hierarchyID(root))),
        Seq(t.Synthetic)
      ).copiedFrom(rcd)
    }

    val refSort = new t.ADTSort(refID, Seq(),
      concreteClasses.filter(cd => hierarchyOf(cd.id).isEmpty).map(constructor(_, refID)) ++
      hierarchyRoots.map { root =>
        new t.ADTConstructor(hierarchyBox(root), refID, Seq(t.ValDef(hierarchyValue(root), hierarchy(root))))
      } ++ symbols.sorts.values.toSeq.map { sort =>
        new t.ADTConstructor(adt(sort.id), refID, Seq(t.ValDef(
          adtValue(sort.id),
          t.ADTType(sort.id, sort.typeArgs.map(tp => ref.copiedFrom(tp))).copiedFrom(sort)
        ).copiedFrom(sort))).copiedFrom(sort)
      } ++ funSizes.map { i =>
        new t.ADTConstructor(fun(i), refID, Seq(t.ValDef(funValue(i), t.FunctionType((1 to i).map(_ => ref), ref))))
      } ++ tplSizes.map { i =>
        new t.ADTConstructor(tpl(i), refID, Seq(t.ValDef(tplValue(i), t.TupleType((1 to i).map(_ => ref)))))
      } ++ bvSizes.map { case ss @ (signed, size) =>
        new t.ADTConstructor(bv(ss), refID, Seq(t.ValDef(bvValue(ss), t.BVType(signed, size))))
      } ++ fpSizes.map { case es @ (exponent, significand) =>
        new t.ADTConstructor(fp(es), refID, Seq(t.ValDef(fpValue(es), t.FPType(exponent, significand))))
      } ++ Seq(
        new t.ADTConstructor(int,  refID, Seq(t.ValDef(intValue,  t.IntegerType()))),
        new t.ADTConstructor(bool, refID, Seq(t.ValDef(boolValue, t.BooleanType()))),
        new t.ADTConstructor(char, refID, Seq(t.ValDef(charValue, t.CharType()))),
        new t.ADTConstructor(real, refID, Seq(t.ValDef(realValue, t.RealType()))),
        new t.ADTConstructor(str,  refID, Seq(t.ValDef(strValue,  t.StringType()))),
        new t.ADTConstructor(arr,  refID, Seq(t.ValDef(arrValue,  t.ArrayType(ref)))),
        new t.ADTConstructor(set,  refID, Seq(t.ValDef(setValue,  t.SetType(ref)))),
        new t.ADTConstructor(bag,  refID, Seq(t.ValDef(bagValue,  t.BagType(ref)))),
        new t.ADTConstructor(map,  refID, Seq(t.ValDef(mapValue,  t.MapType(ref, ref)))),
        new t.ADTConstructor(unit, refID, Seq()),
        new t.ADTConstructor(open, refID, Seq(t.ValDef(openValue, t.IntegerType())))
      ), Seq(t.Synthetic))

    def transform(fd: s.FunDef): t.FunDef = emptyScope.transform(fd)

    def transform(sort: s.ADTSort): t.ADTSort = emptyScope.transform(sort)

    def functions: Seq[t.FunDef] =
      symbols.classes.keys.toSeq.flatMap(id => Seq(classInstance(id)(using this), classUnapply(id)(using this))) ++
      symbols.sorts.keys.flatMap(id => Seq(sortInstance(id)(using this), sortConvert(id)(using this))) ++
      OptionSort.functions ++ Seq(unapplyAny(using this), box, unbox)

    private def box: t.FunDef = {
      val tp = t.TypeParameter.fresh("T")
      // An uninterpreted function of `x` (see `InoxEncoder`)
      new t.FunDef(boxID, Seq(t.TypeParameterDef(tp)), Seq("x" :: tp), ref,
        t.Choose("res" :: ref, t.BooleanLiteral(true)), Seq(t.Synthetic, t.DropVCs))
    }

    private def unbox: t.FunDef = {
      val tp = t.TypeParameter.fresh("T")
      new t.FunDef(unboxID, Seq(t.TypeParameterDef(tp)), Seq("x" :: ref), tp,
        t.Choose("res" :: tp, t.BooleanLiteral(true)), Seq(t.Synthetic, t.DropVCs))
    }

    def sorts: Seq[t.ADTSort] =
      OptionSort.sorts ++ hierarchySorts :+ refSort

    /** Duplicate function [[encoded]] that was derived from [[original]] into
     *  another function without the reified type parameters and an empty body.
     *  The post of [[encoded]] is then modified to assert that its result
     *  is equals to the result of this new function, when applied
     *  to (non-type args) parameters. This allows the solver to deduce that the
     *  reified type parameters themselves do not influence the result of a call
     *  to [[encoded]], something that is needed eg., in the presence of GADTs where
     *  equivalent calls to the same method via both the top-level dispatcher,
     *  and a concrete implementation can carry different reified type parameters.
     */
    def createTypeArgsElimWitness(encoded: t.FunDef, original: s.FunDef): Seq[t.FunDef] = {
      def dropRefinements(tpe: t.Type): t.Type = {
        t.typeOps.preMap {
          // The base type may itself be a refinement, which `preMap` doesn't traverse
          case t.RefinementType(base, _) => Some(dropRefinements(base.tpe))
          case _ => None
        } (tpe)
      }

      val reifiedTypeArgsCount = encoded.params.size - original.params.size
      assert(reifiedTypeArgsCount > 0)

      val elimParams = encoded.params
        .drop(reifiedTypeArgsCount)
        .map(vd => vd.copy(tpe = dropRefinements(vd.tpe)))

      val eliminated = t.exprOps.freshenSignature(new t.FunDef(
        original.id.freshen,
        encoded.tparams,
        elimParams,
        dropRefinements(encoded.returnType),
        t.NoTree(dropRefinements(encoded.returnType)),
        Seq(t.Derived(Some(original.id)))
      ).copiedFrom(encoded))

      val specced = t.exprOps.BodyWithSpecs(encoded.fullBody)
      val (vd, post) = specced.getSpec(t.exprOps.PostconditionKind) match {
        case Some(t.exprOps.Postcondition(Lambda(Seq(vd), post))) => (vd, post)
        case Some(t.exprOps.Postcondition(l @ Lambda(_, _))) =>
          sys.error(s"Unexpected number of params for postcondition lambda: $l")
        case None => (
          t.ValDef.fresh("res", encoded.returnType),
          t.BooleanLiteral(true).copiedFrom(encoded.fullBody)
        )
      }

      val newPostLambda = t.Lambda(Seq(vd),
        t.and(
          post,
          t.Annotated(
            t.Equals(
              vd.toVariable.copiedFrom(post),
              t.FunctionInvocation(
                eliminated.id,
                encoded.tparams.map(_.tp),
                encoded.params.drop(reifiedTypeArgsCount).map(_.toVariable.copiedFrom(post))
              ).copiedFrom(post)
            ).copiedFrom(post),
            Seq(t.DropConjunct)
          ).copiedFrom(post)
        )
      )
      val newPost = t.exprOps.Postcondition(newPostLambda).setPos(post.getPos)

      val newBody = specced.withSpec(newPost).reconstructed
      Seq(encoded.copy(fullBody = newBody), eliminated)
    }
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): (t.Symbols, OOAllSummaries) = {
    val (exSyms, summary) = super.extractSymbols(context, symbols)
    val synthetic = context.functions
    // The definitions of conversions and codes may use more conversions and codes
    val sorts = exSyms.sorts.values ++ context.sorts
    var convs = sortFunDefinitions(exSyms.functions.values ++ synthetic, Set.empty)(using context)
    var (codeSort, isOf) = codeDefinitions(exSyms.functions.values ++ synthetic ++ convs, sorts)(using context)
    var more = sortFunDefinitions(Seq(isOf), convs.map(_.id).toSet)(using context)
    while (more.nonEmpty) {
      convs ++= more
      val (newSort, newIsOf) = codeDefinitions(exSyms.functions.values ++ synthetic ++ convs, sorts)(using context)
      codeSort = newSort
      isOf = newIsOf
      more = sortFunDefinitions(Seq(isOf), convs.map(_.id).toSet)(using context)
    }
    val newSymbols = exSyms
      .withFunctions(synthetic ++ convs :+ isOf)
      .withSorts(context.sorts :+ codeSort)

    // newSymbols.ensureWellFormed

    val dependencies: Set[Identifier] =
      (symbols.functions.keySet ++ symbols.sorts.keySet)
        .flatMap(id => newSymbols.dependencies(id) + id)

    val independentSymbols = t.NoSymbols
      .withFunctions(newSymbols.functions.values.toSeq.filter(fd => dependencies(fd.id)))
      .withSorts(newSymbols.sorts.values.toSeq.filter(sort => dependencies(sort.id)))

    // independentSymbols.ensureWellFormed

    val constructors: Set[Identifier] = {
      import independentSymbols.{given, _}

      var constructors: Set[Identifier] = Set.empty
      val traverser = new t.ConcreteStainlessSelfTreeTraverser {
        override def traverse(expr: t.Expr): Unit = expr match {
          case t.IsTyped(t.ADT(id, tps, es), t.ADTType(`refID`, _)) => constructors += id; super.traverse(expr)
          case t.IsConstructor(t.IsTyped(e, t.ADTType(`refID`, _)), id) => constructors += id; super.traverse(expr)
          case t.ADTSelector(t.IsTyped(e, t.ADTType(`refID`, _)), id) =>
            constructors ++= context.refSort.constructors.find(_.fields.exists(_. id == id)).map(_.id)
            super.traverse(expr)
          case _ => super.traverse(expr)
        }

        override def traverse(pat: t.Pattern): Unit = pat match {
          case t.ADTPattern(_, id, _, _) if getConstructor(id).sort == refID => constructors += id; super.traverse(pat)
          case _ => super.traverse(pat)
        }
      }

      independentSymbols.functions.values.foreach(traverser.traverse)
      independentSymbols.sorts.values.foreach(traverser.traverse)
      constructors
    }

    val result = t.NoSymbols
      .withFunctions(independentSymbols.functions.values.toSeq)
      .withSorts(independentSymbols.sorts.values.toSeq)
      .withSorts(Seq(new t.ADTSort(refID, Seq(), // overrides refSort in `independentSymbols.sorts`
        context.refSort.constructors.filter(cons => cons.id == open || constructors(cons.id)),
        context.refSort.flags)
      ))

    // result.ensureWellFormed
    (result, summary)
  }

  // The computation of which type parameters must be rewritten considers all
  // dependencies, so we use a dependency cache for function transformations
  override protected val funCache = new ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]({
    (fd, context) => getDependencyKey(fd.id)(using context.symbols)
  })

  // Sort transformations are straightforward and can be simply cached
  override protected val sortCache = new SimpleCache[s.ADTSort, (SortResult, SortSummary)]

  // Classes are simply dropped by this phase, so any cache is valid here
  override protected val classCache = new SimpleCache[s.ClassDef, (ClassResult, ClassSummary)]

  // Type definitions are simply dropped by this phase, so any cache is valid here
  override protected val typeDefCache = new SimpleCache[s.TypeDef, (TypeDefResult, TypeDefResult)]

  enum FunctionSummary {
    case Transformed(fid: Identifier)
    case Untransformed(fid: Identifier)
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (Seq[t.FunDef], FunctionSummary) = {
    val encoded = context.transform(fd)

    // If function has gained new parameters for reifed types,
    // we create a dummy version of it without any type arguments
    // as a witness that type arguments do not influence the result
    // of the computation of its invocation.
    if (encoded.params.size > fd.params.size) {
      (context.createTypeArgsElimWitness(encoded, fd), FunctionSummary.Transformed(fd.id))
    } else {
      val unchanged = encoded.id == fd.id && encoded.tparams == fd.tparams && encoded.params == fd.params &&
        encoded.returnType == fd.returnType && encoded.flags == fd.flags && encoded.fullBody == fd.fullBody
      val summary = if (unchanged) FunctionSummary.Untransformed(fd.id) else FunctionSummary.Transformed(fd.id)
      (Seq(encoded), summary)
    }
  }

  enum SortSummary {
    case Transformed(sid: Identifier)
    case Untransformed(sid: Identifier)
  }
  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): (t.ADTSort, SortSummary) = {
    val encoded = context.transform(sort)
    val unchanged = encoded.id == sort.id && encoded.tparams == sort.tparams
      && encoded.flags == sort.flags && encoded.constructors == sort.constructors
    val summary = if (unchanged) SortSummary.Untransformed(sort.id) else SortSummary.Transformed(sort.id)
    (encoded, summary)
  }

  // Classes are simply dropped by this extraction phase
  override protected type ClassResult = Unit
  override protected type ClassSummary = Identifier // To record that the Class went through TypeEncoding
  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): (ClassResult, ClassSummary) = ((), cd.id)
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[Unit]): t.Symbols = symbols

  // Type definitions are simply dropped by this extraction phase
  override protected type TypeDefResult = Unit
  override protected type TypeDefSummary = Unit
  override protected def extractTypeDef(context: TransformerContext, cd: s.TypeDef): (TypeDefResult, TypeDefSummary) = ((), ())
  override protected def registerTypeDefs(symbols: t.Symbols, typeDefs: Seq[Unit]): t.Symbols = symbols

  override protected def combineSummaries(summaries: AllSummaries): ExtractionSummary = {
    val (fns, sorts, classes) = summaries match {
      case s: OOAllSummaries => (s.fnsSummary, s.sortsSummary, s.classesSummaries)
      case s: AllSummaries => (s.fnsSummary, s.sortsSummary, Seq.empty)
    }
    val affectedFns = fns.collect { case FunctionSummary.Transformed(fid) => fid }.toSet
    val affectedSorts = sorts.collect { case SortSummary.Transformed(sid) => sid }.toSet
    ExtractionSummary.Leaf(TypeEncoding)(TypeEncoding.SummaryData(affectedFns, affectedSorts, classes.toSet))
  }
}

object TypeEncoding extends ExtractionPipelineCreator {
  case class SummaryData(affectedFns: Set[Identifier] = Set.empty, affectedSorts: Set[Identifier] = Set.empty, classes: Set[Identifier] = Set.empty) {
    def ++(other: SummaryData): SummaryData =
      SummaryData(affectedFns ++ other.affectedFns, affectedSorts ++ other.affectedSorts, classes ++ other.classes)
    def hasRun: Boolean = affectedFns.nonEmpty || affectedSorts.nonEmpty || classes.nonEmpty
  }
  override val name: String = "TypeEncoding"

  def apply(ts: Trees, tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends TypeEncoding(s, t)
    new Impl(ts, tt)
  }
}
