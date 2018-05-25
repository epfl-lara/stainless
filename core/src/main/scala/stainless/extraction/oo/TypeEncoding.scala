/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._
import scala.collection.mutable.{Map => MutableMap}

trait TypeEncoding
  extends PipelinePhase
     with SimpleSorts
     with SimpleFunctions
     with oo.CachingPhase
     with utils.SyntheticSorts { self =>

  val s: Trees
  val t: imperative.Trees

  import t._
  import t.dsl._
  import s.TypeParameterWrapper

  private[this] def encodeName(s: String): String = s.replace("[", "<").replace("]", ">")

  private[this] implicit class TypeWrapper(tpe: s.Type)(implicit symbols: s.Symbols) {
    def lub(that: s.Type): s.Type = symbols.leastUpperBound(tpe, that)
    def glb(that: s.Type): s.Type = symbols.greatestLowerBound(tpe, that)
  }


  /* ====================================
   *             REF-TYPES ADT
   * ==================================== */

  private[this] val objSort = mkSort(FreshIdentifier("Object"))()(_ => Seq(
    (FreshIdentifier("Object"), Seq("ptr" :: IntegerType()))
  ))
  private[this] val obj = T(objSort.id)()
  private[this] val Seq(objCons) = objSort.constructors
  private[this] val Seq(objPtr)  = objCons.fields.map(_.id)


  /* ====================================
   *        TYPE ADT IDENTIFIERS
   * ==================================== */

  /* Identifier for the base `Type` sort */
  private[this] val tpeID = FreshIdentifier("Type")
  private[this] val tpe   = T(tpeID)()


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
  private[this] val seqID = FreshIdentifier("Seq")
  private[this] val seq   = T(seqID)()

  private[this] val head = FreshIdentifier("head")
  private[this] val tail = FreshIdentifier("tail")

  private[this] val seqSort = mkSort(seqID)()(_ => Seq(
    (FreshIdentifier("Cons"), Seq(ValDef(head, tpe), ValDef(tail, seq))),
    (FreshIdentifier("Nil"), Seq())
  ))
  private[this] val Seq(cons, nil) = seqSort.constructors

  private[this] def mkSeq(es: Seq[Expr]): Expr = es.foldRight(nil())((h, t) => cons(h, t))
  private[this] def seqAt(s: Expr, i: Int): Expr =
    if (i <= 0) Assume(s is cons, s.getField(head))
    else Assume(s is cons, seqAt(s.getField(tail), i - 1))


  /* ====================================
   *           TYPE ADTS
   * ==================================== */

  private[this] val tpeSort = mkSort(tpeID)()(_ => Seq(
    /* Bottom type, corresponds to Scala's {{{Nothing}}} */
    (FreshIdentifier("Bot"), Seq()),

    /* Top type, corresponds to Scala's {{{Any}}} */
    (FreshIdentifier("Top"), Seq()),

    /* Refinement type {{{ { v: tpe | p } }}} */
    (FreshIdentifier("Refinement"), Seq("pred" :: (obj =>: BooleanType()))),

    /* Class type, corresponds to a class definition in Scala:
     * {{{
     * class A[T1,...,Tn] extends C1[Ti,...,Tj] with ... with CN[Tk,...,Tl]
     * }}}
     * Note that `T1` to `Tn` can be variant and have type bounds.
     *
     * "id" field corresponds to `A` name
     * "tps" field corresponds to `T1,...,Tn` type parameters */
    (FreshIdentifier("Class"), Seq("id" :: IntegerType(), "tps" :: seq)),

    /* ADT type, corresponds to a datatype definition in Scala:
     * {{{
     * case class A[T1,...,Tn] extends B[T1,...,Tn]
     * }}}
     * Note that `T1` to `Tn` must be invariant here.
     *
     * "id" field corresponds to `A` name
     * "tps" field corresponds to `T1,...,Tn` type parameters */
    (FreshIdentifier("Adt"), Seq("id" :: IntegerType(), "tps" :: seq)),

    /* Array type, corresponds to {{{Array[base]}}} in Scala */
    (FreshIdentifier("Array"), Seq("base" :: tpe)),

    /* Set type, corresponds to {{{Set[base]}}} in Scala */
    (FreshIdentifier("Set"), Seq("base" :: tpe)),

    /* Bag type, corresponds to {{{Bag[base]}}} in Scala */
    (FreshIdentifier("Bag"), Seq("base" :: tpe)),

    /* Map type, corresponds to {{{Map[from,to}}} in Scala */
    (FreshIdentifier("Map"), Seq("from" :: tpe, "to" :: tpe)),

    /* Function type, corresponds to {{{(From1,...,FromN) => To}}} in Scala */
    (FreshIdentifier("Function"), Seq("from" :: seq, "to" :: tpe)),

    /* Tuple type, corresponds to {{{(Type1,...,TypeN)}}} in Scala */
    (FreshIdentifier("Tuple"), Seq("tps" :: seq)),

    /* Boolean type, corresponds to {{{Boolean}}} in Scala */
    (FreshIdentifier("Boolean"), Seq()),

    /* Integer type, corresponds to {{{BigInt}}} in Scala */
    (FreshIdentifier("Integer"), Seq()),

    /* Bitvector type, corresponds to {{{Int}}}, {{{Short}}}, {{{Byte}}}, ... in Scala */
    (FreshIdentifier("Bitvector"), Seq("size" :: IntegerType())),

    /* Character type, corresponds to {{{Char}}} in Scala */
    (FreshIdentifier("Char"), Seq()),

    /* Unit type, corresponds to {{{Unit}}} in Scala */
    (FreshIdentifier("Unit"), Seq()),

    /* Unbounded real type */
    (FreshIdentifier("Real"), Seq()),

    /* String type, corresponds to {{{String}}} in Scala */
    (FreshIdentifier("String"), Seq())
  ))

  private[this] val Seq(
    bot, top, ref, cls, adt, arr, set, bag, map, fun, tpl, bool, int, bv, char, unit, real, str
  ) = tpeSort.constructors

  private[this] val Seq(refPred) = ref.fields.map(_.id)
  private[this] val Seq(clsPtr, clsTps) = cls.fields.map(_.id)
  private[this] val Seq(adtPtr, adtTps) = adt.fields.map(_.id)
  private[this] val Seq(arrBase) = arr.fields.map(_.id)
  private[this] val Seq(setBase) = set.fields.map(_.id)
  private[this] val Seq(bagBase) = bag.fields.map(_.id)
  private[this] val Seq(mapFrom, mapTo) = map.fields.map(_.id)
  private[this] val Seq(funFrom, funTo) = fun.fields.map(_.id)
  private[this] val Seq(tplTps) = tpl.fields.map(_.id)
  private[this] val Seq(bvSize) = bv.fields.map(_.id)


  /* ====================================
   *   TRANFORMATION/ENCODING CONTEXT
   * ==================================== */

  protected class TypeScope protected(val tparams: Map[s.TypeParameter, t.Expr])
                                     (implicit val symbols: s.Symbols) extends TransformerWithType {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    override def transform(tp: s.Type): t.Type = tp match {
      case s.NothingType() | s.AnyType() | (_: s.ClassType) | (_: s.RefinementType) => obj

      case (_: s.TypeBounds) | (_: s.UnionType) | (_: s.IntersectionType) =>
        throw MissformedStainlessCode(tp, s"Type $tp should never occur in input.")

      case tp: s.TypeParameter if tparams contains tp => obj

      case tp: s.TypeParameter => super.transform(tp.copy(
        flags = tp.flags.filterNot { case (_: s.Variance | _: s.Bounds) => true case _ => false }
      ).copiedFrom(tp))

      case _ => super.transform(tp)
    }

    override def transform(e: s.Expr, inType: s.Type): t.Expr = e match {
      // @nv: the default `TransformerWithType` will have use a non-widened expected result
      //      type in the lambda and this breaks the assumption of no intersection and union
      //      types occuring as `inType`.
      case s.Lambda(args, body) => symbols.widen(inType) match {
        case ft: s.FunctionType => super.transform(e, ft.copy(to = symbols.widen(ft.to)).copiedFrom(ft))
        case _ => super.transform(e, inType)
      }

      case _ => super.transform(e, inType)
    }
  }

  private[this] object TypeScope {
    def empty(implicit symbols: s.Symbols) = new TypeScope(Map.empty)

    def apply(cd: s.ClassDef, tpe: Expr)(implicit symbols: s.Symbols): TypeScope = {
      val clsParams = cd.tparams.indices.map(i => seqAt(tpe.getField(clsTps), i))
      val newTParams = (cd.tparams.map(_.tp) zip clsParams).toMap
      new TypeScope(newTParams)
    }

    def apply(d: s.ADTSort, tpe: Expr)(implicit symbols: s.Symbols): TypeScope = {
      val adtParams = d.tparams.indices.map(i => seqAt(tpe.getField(adtTps), i))
      val newTParams = (d.tparams.map(_.tp) zip adtParams).toMap
      new TypeScope(newTParams)
    }

    def apply(pairs: Traversable[(s.TypeParameter, t.Expr)])(implicit symbols: s.Symbols): TypeScope =
      new TypeScope(pairs.toMap)
  }

  private[this] def isObject(tpe: s.Type)(implicit scope: TypeScope): Boolean = tpe match {
    case _: s.ClassType => true
    case s.NothingType() | s.AnyType() => true
    case tp: s.TypeParameter => scope.tparams contains tp
    case (_: s.UnionType) | (_: s.IntersectionType) => true
    case _ => false
  }

  private[this] def isSimple(tpe: s.Type)(implicit scope: TypeScope): Boolean = !s.typeOps.exists(isObject)(tpe)


  /* ====================================
   *          GET-TYPE FUNCTION
   * ==================================== */

  private[this] val typeField = FreshIdentifier("getType")
  private[this] val typeFunction = mkFunDef(typeField, Unchecked)()(_ => (
    Seq("e" :: obj), tpe, { case Seq(e) => choose("res" :: tpe)(_ => E(true)) }))

  private[this] val typeOf = (e: Expr) => FunctionInvocation(typeField, Seq(), Seq(e))


  /* ====================================
   *  SUBTYPING/INSTANCEOF FUNCTION IDS
   * ==================================== */

  private[this] val subtypeID = FreshIdentifier("isSubtypeOf")
  private[this] def subtypeOf(e1: Expr, e2: Expr) = FunctionInvocation(subtypeID, Seq(), Seq(e1, e2))

  private[this] val instanceID = FreshIdentifier("isInstanceOf")
  private[this] def instanceOf(e1: Expr, e2: Expr) = FunctionInvocation(instanceID, Seq(), Seq(e1, e2))


  /* ====================================
   *         UNBOXING FUNCTIONS
   * ==================================== */

  private[this] val unwrapFunction: t.FunDef =
    mkFunDef(FreshIdentifier("unwrap"), Unchecked)("T") { case Seq(aT) =>
      (Seq("x" :: obj), aT, { case Seq(x) => choose("res" :: aT)(_ => E(true)) })
    }

  private[this] def unwrap(e: t.Expr, expected: t.Type): t.Expr = {
    if (expected == obj) e
    else FunctionInvocation(unwrapFunction.id, Seq(expected), Seq(e)).copiedFrom(e)
  }


  /* ====================================
   *           TYPE ENCODING
   * ==================================== */

  private[this] def encodeType(tpe: s.Type)(implicit scope: TypeScope): t.Expr = tpe match {
    case s.AnyType() => top()
    case s.NothingType() => bot()
    case s.RefinementType(vd, pred) =>
      val nvd = t.ValDef(vd.id, obj).copiedFrom(vd)
      val npred = t.exprOps.replaceFromSymbols(
        Map(scope.transform(vd) -> unwrap(nvd.toVariable, scope.transform(vd.tpe))),
        scope.transform(pred))
      ref(t.Lambda(Seq(nvd), t.and(instanceOf(nvd.toVariable, encodeType(vd.tpe)), npred)))
    case s.ClassType(id, tps) => cls(IntegerLiteral(id.globalId), mkSeq(tps map encodeType))
    case s.ADTType(id, tps) => adt(IntegerLiteral(id.globalId), mkSeq(tps map encodeType))
    case s.ArrayType(base) => arr(encodeType(base))
    case s.SetType(base) => set(encodeType(base))
    case s.BagType(base) => bag(encodeType(base))
    case s.MapType(from, to) => map(encodeType(from), encodeType(to))
    case s.TupleType(tps) => tpl(mkSeq(tps map encodeType))
    case s.FunctionType(from, to) => fun(mkSeq(from map encodeType), encodeType(to))
    case tp: s.TypeParameter if scope.tparams contains tp => scope.tparams(tp)
    case tp: s.TypeParameter => top()
    case s.BooleanType() => bool()
    case s.IntegerType() => int()
    case s.BVType(size) => bv(IntegerLiteral(size))
    case s.CharType() => char()
    case s.UnitType() => unit()
    case s.RealType() => real()
    case s.StringType() => str()
    case _ => scala.sys.error("Unexpected type " + tpe)
  }


  /* ====================================
   *          BOXING FUNCTION
   * ==================================== */

  private[this] val wrapFunction: t.FunDef =
    mkFunDef(FreshIdentifier("wrap"), Unchecked)("T") { case Seq(aT) =>
      (Seq("x" :: aT, "tpe" :: tpe), obj, { case Seq(x, tpe) =>
        choose("res" :: obj)(res => unwrap(res, aT) === x && typeOf(res) === tpe)
      })
    }

  private[this] def wrap(e: t.Expr, tpe: s.Type)(implicit scope: TypeScope): t.Expr = {
    if (isObject(tpe)) e
    else FunctionInvocation(
      wrapFunction.id,
      Seq(scope.transform(tpe)),
      Seq(e, encodeType(tpe))
    ).copiedFrom(e)
  }


  /* ====================================
   *         SUBTYPING FUNCTION
   * ==================================== */

  private[this] def isSubtypeOfClass(cd: s.ClassDef, tp1: Expr, tp2: Expr): Expr = {
    def rec(tparams: Seq[s.TypeParameter], seq1: Expr, seq2: Expr): Expr = tparams match {
      case tp +: xs =>
        val (t1, t2) = (seq1.getField(head), seq2.getField(head))
        val cond = if (tp.isCovariant) subtypeOf(t1, t2)
      else if (tp.isContravariant) subtypeOf(t2, t1)
      else t1 === t2
      (seq1 is cons) &&
      (seq2 is cons) &&
      cond &&
      rec(xs, seq1.getField(tail), seq2.getField(tail))
      case Seq() => (seq1 is nil) && (seq2 is nil)
    }

    tp1.getField(clsPtr) === IntegerLiteral(cd.id.globalId) &&
    tp2.getField(clsPtr) === IntegerLiteral(cd.id.globalId) &&
    rec(cd.typeArgs, tp1.getField(clsTps), tp2.getField(clsTps))
  }

  private[this] def subtypeFunction(implicit symbols: s.Symbols): t.FunDef = mkFunDef(subtypeID, Unchecked)()(_ => (
    Seq("tp1" :: tpe, "tp2" :: tpe), BooleanType(), {
      case Seq(tp1, tp2) => Seq(
        (tp2 is top) -> E(true),
        (tp1 is bot) -> E(true),
        (tp1 is ref) -> forall("x" :: obj)(x => tp1.getField(refPred)(x) ==> instanceOf(x, tp2)),
        (tp2 is ref) -> forall("x" :: obj)(x => instanceOf(x, tp1) ==> tp2.getField(refPred)(x)),
        (tp1 is cls) -> (
          (tp2 is cls) &&
          symbols.classes.values.foldRight(
            IfExpr(andJoin(symbols.classes.values.filter(_.flags contains s.IsSealed).toSeq.map {
              cd => !(tp2.getField(clsPtr) === IntegerLiteral(cd.id.globalId))
            }), choose("res" :: BooleanType())(_ => E(true)), E(false)): Expr
          ) {
            case (cd, elze) => IfExpr(
              tp1.getField(clsPtr) === IntegerLiteral(cd.id.globalId),
              isSubtypeOfClass(cd, tp1, tp2) ||
              orJoin(cd.parents.map(ct => subtypeOf(encodeType(ct)(TypeScope(cd, tp1)), tp2))),
              elze
            )
          }
        ),
        (tp1 is adt) -> (
          (tp2 is adt) &&
          symbols.sorts.values.foldRight(E(false)) {
            case (d, elze) => IfExpr(
              tp1.getField(adtPtr) === IntegerLiteral(d.id.globalId),
              (tp2.getField(adtPtr) === IntegerLiteral(d.id.globalId)) &&
              tp1.getField(adtTps) === tp2.getField(adtTps),
              elze
            )
          }
        ),
        (tp1 is tpl) -> (
          (tp2 is tpl) && (
            (
              (tp1.getField(tplTps) is nil) &&
              (tp2.getField(tplTps) is nil)
            ) || (
              (tp1.getField(tplTps) is cons) &&
              (tp2.getField(tplTps) is cons) &&
              subtypeOf(
                tp1.getField(tplTps).getField(head),
                tp2.getField(tplTps).getField(head)
              ) &&
              subtypeOf(
                tpl(tp1.getField(tplTps).getField(tail)),
                tpl(tp2.getField(tplTps).getField(tail))
              )
            )
          )
        ),
        (tp1 is fun) -> (
          (tp2 is fun) && (
            (
              (tp1.getField(funFrom) is nil) &&
              (tp2.getField(funFrom) is nil) &&
              subtypeOf(
                tp1.getField(funTo),
                tp2.getField(funTo)
              )
            ) || (
              (tp1.getField(funFrom) is cons) &&
              (tp2.getField(funFrom) is cons) &&
              subtypeOf( // contravariant!
                tp2.getField(funFrom).getField(head),
                tp1.getField(funFrom).getField(head)
              ) &&
              subtypeOf(
                fun(tp1.getField(funFrom).getField(tail), tp1.getField(funTo)),
                fun(tp2.getField(funFrom).getField(tail), tp2.getField(funTo))
              )
            )
          )
        )
      ).foldRight((tp1 === tp2): Expr) {
        case ((cond, thenn), elze) => IfExpr(cond, thenn, elze)
      }
    }))


  /* ====================================
   *     REF-TYPE FIELDS & WRAPPERS
   * ==================================== */

  private case class ClassInfo(constructor: t.FunDef, fields: Seq[t.FunDef])
  private[this] val infoCache = new ExtractionCache[s.ClassDef, ClassInfo]
  private[this] def classInfo(id: Identifier)(implicit symbols: s.Symbols): ClassInfo = {
    val cd = symbols.getClass(id)
    infoCache.cached(cd, symbols) {
      val fields = cd.fields.map { vd =>
        val id = vd.id.freshen
        val arg = ValDef(FreshIdentifier("e"), obj)
        implicit val scope = TypeScope(cd, typeOf(arg.toVariable))

        val resTpe = scope.transform(vd.tpe)
        mkFunDef(id, Unchecked)()(_ => (Seq(arg), resTpe, {
          case Seq(_) => choose("res" :: resTpe) { res =>
            if (isObject(vd.tpe)) {
              instanceOf(res, encodeType(vd.tpe))
            } else {
              E(true)
            }
          }
        }))
      }

      val constructor = {
        val ct = s.ClassType(cd.id, cd.typeArgs)
        val tparamParams = cd.tparams.map(tpd => t.ValDef(tpd.id.freshen, tpe).copiedFrom(tpd))
        implicit val scope = TypeScope(cd.typeArgs zip tparamParams.map(_.toVariable))
        val paramParams = cd.fields.map(vd => t.ValDef(vd.id.freshen, scope.transform(vd.tpe)))

        mkFunDef(cd.id.freshen, Unchecked)()(_ => (
          tparamParams ++ paramParams, obj, { case args =>
            choose(ValDef(FreshIdentifier("ptr", true), obj, Seq(Unchecked))) { res =>
              typeOf(res) === encodeType(ct) &&
              andJoin((fields zip args.drop(tparamParams.size)).map { case (fd, e) =>
                FunctionInvocation(fd.id, Seq(), Seq(res)) === e
              })
            }
          }
        ))
      }

      ClassInfo(constructor, fields)
    }
  }

  private[this] def constructor(cid: Identifier)(implicit symbols: s.Symbols): t.FunDef = {
    classInfo(cid).constructor
  }

  private[this] def field(cid: Identifier, id: Identifier)(implicit symbols: s.Symbols): t.FunDef = {
    (symbols.getClass(cid).fields zip classInfo(cid).fields).collectFirst { case (vd, fd) if vd.id == id => fd }.get
  }

  private[this] def getField(cid: Identifier, id: Identifier)(e: t.Expr)(implicit symbols: s.Symbols): t.Expr = {
    t.FunctionInvocation(field(cid, id).id, Seq(), Seq(e))
  }


  /* ====================================
   *         INSTANCEOF FUNCTION
   * ==================================== */

  def instanceFunction(implicit symbols: s.Symbols): t.FunDef = mkFunDef(instanceID, Unchecked)()(_ => (
    Seq("e" :: obj, "tp2" :: tpe), BooleanType(), {
      case Seq(e, tp2) => let("tp1" :: tpe, typeOf(e))(tp1 => Seq(
        (tp2 is bot) -> E(false),
        (tp2 is top) -> !(tp1 is bot),
        (tp2 is ref) -> tp2.getField(refPred)(e),
        (tp2 is cls) -> (
          (tp1 is cls) &&
          symbols.classes.values.toSeq.foldRight(E(false)) { case (cd, elze) =>
            val optCons = if (cd.flags contains s.IsAbstract) None else Some(
              isSubtypeOfClass(cd, tp1, tp2) &&
              e === t.FunctionInvocation(
                constructor(cd.id).id,
                Seq(),
                cd.tparams.indices.map(i => seqAt(tp1.getField(clsTps), i)) ++
                cd.fields.map(vd => getField(cd.id, vd.id)(e))
              )
            )

            IfExpr(
              tp2.getField(clsPtr) === IntegerLiteral(cd.id.globalId),
              orJoin(
                optCons.toSeq ++
                cd.typed(symbols).children.map(c => instanceOf(e, encodeType(c.toType)(TypeScope(cd, tp2)))) ++
                (if (cd.flags contains s.IsSealed) None else Some(subtypeOf(tp1, tp2)))
              ),
              elze
            )
          }
        )
      ).foldRight(subtypeOf(tp1, tp2): Expr) {
        case ((cond, thenn), elze) => IfExpr(cond, thenn, elze)
      }).copiedFrom(e)
    }))


  /* ====================================
   *     GENERAL WRAPPING/UNWRAPPING
   * ==================================== */

  val unificationCache: MutableMap[(t.Type, t.Type), t.FunDef] = MutableMap.empty
  def unificationFunctions: Seq[t.FunDef] = unificationCache.values.toSeq

  /* Transforms `e` of type `tpe` into an expression of type `expected`.
   * Note that neither `tpe` nor `expected` will contain type parameters so we can maintain a global
   * cache of the ADT unification functions. */
  def unifyTypes(e: t.Expr, tpe: s.Type, expected: s.Type)(tpeScope: TypeScope, expectedScope: TypeScope): t.Expr = {

    val unifications: MutableMap[(t.Type, t.Type), Identifier] = MutableMap.empty

    def rec(e: t.Expr, lo: s.Type, hi: s.Type)(loScope: TypeScope, hiScope: TypeScope): t.Expr = {
      if (lo == hi) e
      else if (isObject(lo)(loScope) && isObject(hi)(hiScope)) e
      else if (isObject(lo)(loScope) && isSimple(hi)(hiScope)) unwrap(e, hiScope transform hi)
      else if (isSimple(lo)(loScope) && isObject(hi)(hiScope)) wrap(e, lo)(loScope)
      else ((e, lo, hi) match {
        case (Lambda(args, body), s.FunctionType(from1, to1), s.FunctionType(from2, to2)) =>
          val newArgs = (args zip from2).map { case (vd, tpe) => vd.copy(tpe = hiScope.transform(tpe)).copiedFrom(vd) }
          val unifiedArgs = newArgs zip (from1 zip from2) map { case (vd, (tp1, tp2)) => rec(vd.toVariable, tp2, tp1)(hiScope, loScope) }
          val newBody = rec(exprOps.replaceFromSymbols((args.map(_.toVariable) zip unifiedArgs).toMap, body), to1, to2)(loScope, hiScope)
          Lambda(newArgs, newBody).copiedFrom(e)

        case (_, s.FunctionType(from1, to1), s.FunctionType(from2, to2)) =>
          val newArgs = from2.map(tp => ValDef.fresh("x", hiScope.transform(tp), true).copiedFrom(tp))
          val unifiedArgs = newArgs zip (from1 zip from2) map { case (vd, (tp1, tp2)) => rec(vd.toVariable, tp2, tp1)(hiScope, loScope) }
          Lambda(newArgs, rec(Application(e, unifiedArgs).copiedFrom(e), to1, to2)(loScope, hiScope)).copiedFrom(e)

        case (Tuple(es), s.TupleType(tps1), s.TupleType(tps2)) =>
          Tuple(es zip (tps1 zip tps2) map { case (e, (tp1, tp2)) => rec(e, tp1, tp2)(loScope, hiScope) }).copiedFrom(e)

        case (_, s.TupleType(tps1), s.TupleType(tps2)) =>
          Tuple((tps1 zip tps2).zipWithIndex map {
            case ((tp1, tp2), i) => rec(TupleSelect(e, i + 1).copiedFrom(e), tp1, tp2)(loScope, hiScope)
          }).copiedFrom(e)

        /*
        case (_, _: s.TypeParameter, _) | (_, _, _: s.TypeParameter) =>
          rec(wrap(e, lo)(loScope), s.AnyType(), hi)(loScope, hiScope)
        */

        /*
      case (tpe1 @ ADTType(id1, tps1), tpe2 @ ADTType(id2, tps2)) if id1 == id2 =>
        val id = unifications.get(tpe1 -> tpe2)
          .orElse(unificationCache.get(tpe1 -> tpe2).map(_.id))
          .getOrElse {
            val sort = syms.getSort(id1)
            val id = FreshIdentifier(encodeName("unify_" + tpe1 + "_" + tpe2))
            unifications += (tpe1, tpe2) -> id
            unificationCache += (tpe1, tpe2) -> mkFunDef(id, Unchecked)()(_ => (
              Seq("e" :: tpe1), tpe2, { case Seq(e) =>
                val scope = TypeScope.empty
                val typeArgs = sort.typeArgs.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])
                val condRecons :+ ((_, last)) = sort.constructors.map { cons =>
                  val fields = cons.fields.map { vd =>
                    val ttpe = scope.transform(vd.tpe)
                    def instantiate(tps: Seq[Type]): Type = t.typeOps.instantiateType(ttpe, (typeArgs zip tps).toMap)
                    rec(ADTSelector(e, vd.id).copiedFrom(e), instantiate(tps1), instantiate(tps2))
                  }

                  (IsConstructor(e, cons.id).copiedFrom(e), ADT(cons.id, tps2, fields).copiedFrom(e))
                }

                condRecons.foldRight(last: Expr) { case ((cond, e), elze) => IfExpr(cond, e, elze).copiedFrom(cond) }
              }
            ))
            id
          }

        FunctionInvocation(id, Seq(), Seq(e)).copiedFrom(e)

      case (ArrayType(b1), ArrayType(b2)) => choose(ValDef(FreshIdentifier("res"), hi, Seq(Unchecked)).copiedFrom(e)) {
        res => forall(("i" :: Int32Type().copiedFrom(e)).copiedFrom(e)) {
          i => (rec(ArraySelect(e, i).copiedFrom(e), b1, b2) === ArraySelect(res, i).copiedFrom(e)).copiedFrom(e)
        }.copiedFrom(e)
      }.copiedFrom(e)

      case (SetType(b1), SetType(b2)) => choose(ValDef(FreshIdentifier("res"), hi, Seq(Unchecked)).copiedFrom(e)) {
        res => forall(("x" :: b1).copiedFrom(e)) {
          x => (ElementOfSet(x, e).copiedFrom(e) === ElementOfSet(rec(x, b1, b2), res).copiedFrom(e)).copiedFrom(e)
        }.copiedFrom(e)
      }.copiedFrom(e)

      case (BagType(b1), BagType(b2)) => choose(ValDef(FreshIdentifier("res"), hi, Seq(Unchecked)).copiedFrom(e)) {
        res => forall(("x" :: b1).copiedFrom(e)) {
          x => (MultiplicityInBag(x, e).copiedFrom(e) === MultiplicityInBag(rec(x, b1, b2), res).copiedFrom(e)).copiedFrom(e)
        }.copiedFrom(e)
      }.copiedFrom(e)

      case (MapType(f1, t1), MapType(f2, t2)) => choose(ValDef(FreshIdentifier("res"), hi, Seq(Unchecked)).copiedFrom(e)) {
        res => forall(("x" :: f1).copiedFrom(e)) {
          x => (rec(MapApply(e, x).copiedFrom(e), t1, t2) === MapApply(res, rec(x, f1, f2)).copiedFrom(e)).copiedFrom(e)
        }.copiedFrom(e)
      }.copiedFrom(e)
      */

        case _ => e
      })
    }

    rec(e, tpeScope.symbols.encodableType(tpe), expectedScope.symbols.encodableType(expected))(tpeScope, expectedScope)
  }


  /* ====================================
   *          UNAPPLY FUNCTIONS
   * ==================================== */

  // The computation of `OptionSort.Info` takes uncachable dependencies into account so we
  // can validly use it as a cache key here without risking extraction unsoundness.
  // The `UnapplyInfo` class then contains its own caches for definitions that require
  // dependency checks.
  private[this] val unapplyCache = scala.collection.mutable.Map.empty[OptionSort.Info, UnapplyInfo]
  private[this] def unapplyInfo(implicit symbols: s.Symbols): UnapplyInfo = {
    val info = OptionSort.info
    unapplyCache.getOrElseUpdate(info, UnapplyInfo(symbols, info))
  }

  private case class UnapplyInfo(symbols: s.Symbols, info: OptionSort.Info) {
    protected val implicitSymbols: s.Symbols = symbols
    protected val OptionSort.Info(option, some, none, isEmpty, get) = info

    val unwrapUnapplierFunction: t.FunDef =
      mkFunDef(FreshIdentifier("IsTyped"), Unchecked, IsUnapply(isEmpty, get))("T") { case Seq(aT) =>
        (Seq("thiss" :: tpe, "x" :: obj), T(option)(aT), { case Seq(thiss, x) =>
          if_ (instanceOf(x, thiss)) {
            C(some)(aT)(unwrap(x, aT))
          } else_ {
            C(none)(aT)()
          }
        })
      }

    val instanceUnapplierFunction: t.FunDef =
      mkFunDef(FreshIdentifier("IsTyped"), Unchecked, IsUnapply(isEmpty, get))() { _ =>
        (Seq("thiss" :: tpe, "x" :: obj), T(option)(obj), { case Seq(thiss, x) =>
          if_ (instanceOf(x, thiss)) {
            C(some)(obj)(x)
          } else_ {
            C(none)(obj)()
          }
        })
      }

    def unapplier(tpe: s.Type, sub: t.Pattern)(implicit scope: TypeScope): t.Pattern =
      (if (isObject(tpe)) {
        t.UnapplyPattern(None, Some(encodeType(tpe)), instanceUnapplierFunction.id, Seq(), Seq(sub))
      } else {
        t.UnapplyPattern(None, Some(encodeType(tpe)), unwrapUnapplierFunction.id, Seq(scope.transform(tpe)), Seq(sub))
      }).copiedFrom(sub)

    val classUnapplierCache = new ExtractionCache[s.ClassDef, t.FunDef]
    def classUnapplier(id: Identifier): t.FunDef = {
      val cd = symbols.getClass(id)
      classUnapplierCache.cached(cd, symbols) {
        val arg = t.ValDef(FreshIdentifier("x"), obj)
        implicit val scope = TypeScope(cd, typeOf(arg.toVariable))(symbols)
        val tt = t.tupleTypeWrap(cd.fields.map(vd => if (isObject(vd.tpe)) obj else scope.transform(vd.tpe)))
        mkFunDef(FreshIdentifier(id.name), Unchecked, IsUnapply(isEmpty, get))() { _ =>
          (Seq("thiss" :: tpe, arg), T(option)(tt), { case Seq(thiss, x) =>
            if_ (instanceOf(x, thiss)) {
              C(some)(tt)(t.tupleWrap(cd.fields.map(vd => getField(id, vd.id)(x)(symbols))))
            } else_ {
              C(none)(tt)()
            }
          })
        }
      }
    }

    def unapplyFunctions: Seq[t.FunDef] = {
      val patterns = scala.collection.mutable.Set.empty[Identifier]
      val traverser = new s.TreeTraverser {
        override def traverse(pat: s.Pattern): Unit = pat match {
          case s.ClassPattern(_, ct, _) =>
            patterns += ct.id
            super.traverse(pat)
          case _ => super.traverse(pat)
        }
      }

      symbols.functions.values.foreach(fd => traverser.traverse(fd))

      Seq(unwrapUnapplierFunction, instanceUnapplierFunction) ++ patterns.map(classUnapplier)
    }
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)

  protected class TransformerContext(implicit symbols: s.Symbols) {
    private[this] val unapplies = unapplyInfo(symbols)
    import unapplies._

    private[this] abstract class FunInfo {
      val fun: s.FunAbstraction
      val outer: Option[Scope]
      def rewrite: Boolean
    }

    private[this] case class RewriteInfo(fun: s.FunAbstraction, outer: Option[Scope], tparams: Seq[t.ValDef])
      extends FunInfo { def rewrite = true }
    private[this] case class SimpleInfo(fun: s.FunAbstraction, outer: Option[Scope])
      extends FunInfo { def rewrite = false }

    private[this] class Scope private(
      functions: Map[Identifier, FunInfo],
      tparams: Map[s.TypeParameter, t.Expr],
      graph: DiGraph[s.FunAbstraction, SimpleEdge[s.FunAbstraction]]
    )(implicit symbols: s.Symbols) extends TypeScope(tparams) {
      import symbols.{let => _, _}

      protected implicit val scope = this

      def rewrite(id: Identifier): Boolean = functions(id).rewrite

      private def isSimpleFunction(fun: s.FunAbstraction): Boolean = {
        var simple: Boolean = true
        object traverser extends s.TreeTraverser {
          protected def traverse(pat: s.Pattern, in: s.Type): Unit = pat match {
            case s.WildcardPattern(_) =>
            case s.InstanceOfPattern(_, tpe) if !isSimple(in.getType lub tpe) => simple = false
            case s.ClassPattern(_, _, _) => simple = false
            case s.ADTPattern(ob, id, tps, subs) =>
              val tcons = getConstructor(id, tps)
              if (!isSimple(in lub s.ADTType(tcons.sort.id, tps))) simple = false
              else {
                (subs zip tcons.fields).foreach(p => traverse(p._1, p._2.tpe))
              }

            case s.TuplePattern(ob, subs) => in match {
              case s.TupleType(tps) => (subs zip tps).foreach(p => traverse(p._1, p._2))
              case _ => subs.foreach(traverse(_, s.AnyType()))
            }

            case up @ s.UnapplyPattern(ob, rec, id, tps, subs) =>
              (subs zip up.subTypes(in)) foreach (p => traverse(p._1, p._2))

            case s.LiteralPattern(_, lit) if !isSimple(in.getType lub lit.getType) => simple = false
            case _ =>
          }

          override def traverse(e: s.Expr): Unit = e match {
            case s.ClassConstructor(_, _) => simple = false
            case s.ClassSelector(_, _) => simple = false
            case s.MatchExpr(scrut, cases) => cases.foreach { case s.MatchCase(pat, _, _) => traverse(pat, scrut.getType) }
            case s.IsInstanceOf(e, tpe) if !isSimple(e.getType lub tpe) => simple = false
            case s.AsInstanceOf(e, tpe) if !isSimple(e.getType lub tpe) => simple = false
            case _ => super.traverse(e)
          }

          override def traverse(tpe: s.Type): Unit = tpe match {
            case _ if isObject(tpe) => simple = false
            case _ => super.traverse(tpe)
          }

          override def traverse(flag: s.Flag): Unit = flag match {
            case s.Bounds(_, _) => simple = false
            case _ => super.traverse(flag)
          }
        }

        fun.tparams.foreach(traverser.traverse)
        fun.params.foreach(traverser.traverse)
        traverser.traverse(fun.returnType)
        traverser.traverse(fun.fullBody)
        fun.flags.foreach(traverser.traverse)
        simple
      }

      def withFunctions(funs: Seq[s.FunAbstraction]): Scope = {
        val funMap = funs.map(fun => fun.id -> fun).toMap

        var newGraph = graph
        for (fun1 <- funs; fun2 <- s.exprOps.collect {
          case s.FunInvocation(id, tps, args, _) if functions contains id => Set(functions(id).fun)
          case s.FunInvocation(id, tps, args, _) if funMap contains id => Set(funMap(id))
          case s.MatchExpr(_, cases) => cases.flatMap(cse => s.patternOps.collect {
            case s.UnapplyPattern(_, _, id, _, _) if functions contains id => Set(functions(id).fun)
            case s.UnapplyPattern(_, _, id, _, _) if funMap contains id => Set(funMap(id))
            case _ => Set[s.FunAbstraction]()
          } (cse.pattern)).toSet
          case _ => Set[s.FunAbstraction]()
        } (fun1.fullBody)) newGraph += SimpleEdge(fun1, fun2)

        val baseSimple = funs.filter(isSimpleFunction).toSet
        val fixSimple = inox.utils.fixpoint { (funs: Set[s.FunAbstraction]) =>
          funs.filter(fun => newGraph.transitiveSucc(fun) subsetOf funs)
        } (baseSimple ++ functions.values.collect { case SimpleInfo(fun, _) => fun })

        val newFunctions = functions ++ funs.map(fun => fun.id -> {
          if (fixSimple(fun)) {
            SimpleInfo(fun, Some(this))
          } else {
            val tparamVals = fun.tparams.map(tpd => t.ValDef(tpd.id.freshen, tpe))
            RewriteInfo(fun, Some(this), tparamVals)
          }
        })

        new Scope(newFunctions, tparams, newGraph)
      }

      def in(id: Identifier): Scope = {
        val RewriteInfo(fun, _, vds) = functions(id)
        val newTparams = tparams ++ (fun.tparams zip vds).map(p => p._1.tp -> p._2.toVariable)
        new Scope(functions, newTparams, graph)
      }

      override def transform(e: s.Expr, inType: s.Type): t.Expr = e match {
        case s.ClassConstructor(ct, args) =>
          val encodedTps = ct.tps map encodeType
          val cdScope = TypeScope(ct.tcd.cd.typeArgs zip encodedTps)
          val fd = constructor(ct.id)
          t.FunctionInvocation(fd.id, Seq(),
            encodedTps ++ (ct.tcd.cd.fields zip args).map { case (vd, arg) =>
              unifyTypes(transform(arg), arg.getType, vd.tpe)(this, cdScope)
            }
          ).copiedFrom(e)

        case s.ClassSelector(expr, id) =>
          val s.ClassType(cid, _) = symbols.widen(expr.getType)
          getField(cid, id)(transform(expr)).copiedFrom(e)

        case s.IsInstanceOf(expr, tpe) if isObject(expr.getType lub tpe) =>
          instanceOf(transform(expr), encodeType(tpe)).copiedFrom(e)

        case s.IsInstanceOf(expr, tpe) =>
          t.BooleanLiteral(isSubtypeOf(expr.getType, tpe)).copiedFrom(e)

        case s.AsInstanceOf(expr, tpe) if isObject(expr.getType lub tpe) =>
          val exprType = expr.getType
          val te = transform(expr)
          val check = if (isObject(exprType)) instanceOf(te, encodeType(tpe))
            else subtypeOf(encodeType(exprType), encodeType(tpe))
          val result = unifyTypes(te, exprType, tpe)(this, this)
          t.Assert(check, Some("Cast error"), result).copiedFrom(e)

        case s.AsInstanceOf(expr, tpe) => transform(expr)

        case fi @ s.FunctionInvocation(id, tps, args) if scope rewrite id =>
          val fdScope = this in id
          unifyTypes(
            t.FunctionInvocation(id, Seq(),
              (tps map encodeType) ++ (getFunction(id).params zip args).map { case (vd, arg) =>
                unifyTypes(transform(arg), arg.getType, vd.tpe)(this, fdScope)
              }
            ).copiedFrom(e),
            fi.getType,
            inType
          )(fdScope, this)

        case app @ s.ApplyLetRec(v, tparams, tps, args) if scope rewrite v.id =>
          val appScope = this in v.id
          val fun = functions(v.id).fun
          val vd @ t.ValDef(id, FunctionType(from, to), flags) = appScope.transform(v.toVal)
          val nvd = vd.copy(tpe = FunctionType(tparams.map(_ => tpe) ++ from, to))
          unifyTypes(
            t.ApplyLetRec(nvd.toVariable, Seq(), Seq(),
              (tps map encodeType) ++ (fun.params zip args).map { case (vd, arg) =>
                unifyTypes(transform(arg), arg.getType, vd.tpe)(this, appScope)
              }
            ).copiedFrom(app),
            app.getType,
            inType
          )(appScope, this)

        case app @ s.ApplyLetRec(v, tparams, tps, args) =>
          val appScope = functions(v.id).outer.get
          unifyTypes(t.ApplyLetRec(
            appScope.transform(v.toVal).toVariable,
            tparams map (appScope.transform(_).asInstanceOf[t.TypeParameter]),
            tps map transform,
            args map transform
          ).copiedFrom(e), app.getType, inType)(this, this)

        case s.LetRec(fds, body) =>
          val funs = fds.map(fd => s.Inner(fd))
          val newScope = scope withFunctions funs
          val newFuns = funs.map(fun => transformFunction(fun)(newScope))
          val newBody = newScope.transform(body, inType)
          t.LetRec(newFuns.map(_.toLocal), newBody).copiedFrom(e)

        case e if isObject(e.getType) != isObject(inType) =>
          unifyTypes(transform(e), e.getType, inType)(this, this)

        case _ =>
          super.transform(e, inType)
      }

      override def transform(e: s.Expr): t.Expr = transform(e, symbols.widen(e.getType))

      override def transform(pat: s.Pattern, tpe: s.Type): t.Pattern = pat match {
        case s.WildcardPattern(ob) =>
          t.WildcardPattern(ob map transform).copiedFrom(pat)

        case s.InstanceOfPattern(ob, tp) =>
          if (isObject(tpe lub tp)) {
            unapplier(tp, t.WildcardPattern(ob map transform).copiedFrom(pat))
          } else {
            t.WildcardPattern(ob map transform).copiedFrom(pat)
          }

        case s.ClassPattern(ob, ct, subs) =>
          val id = classUnapplier(ct.id).id
          val rsubs = (subs zip ct.tcd.fields) map { case (sub, vd) => transform(sub, vd.tpe) }
          t.UnapplyPattern(ob map transform, Some(encodeType(ct)), id, Seq(), rsubs).copiedFrom(pat)

        case s.ADTPattern(ob, id, tps, subs) =>
          val tcons = symbols.getConstructor(id, tps)
          val adt = s.ADTType(tcons.sort.id, tps)
          if (isObject(tpe lub adt)) {
            unapplier(adt, transform(pat, adt))
          } else {
            super.transform(pat, tpe)
          }

        case s.TuplePattern(ob, subs) =>
          val tt = s.TupleType(subs map (_ => s.AnyType()))
          if (isObject(tpe lub tt)) {
            unapplier(tt, transform(pat, tt))
          } else {
            super.transform(pat, tpe)
          }

        case up @ s.UnapplyPattern(ob, rec, id, tps, subs) =>
          if (rewrite(id)) {
            val rec = if (tps.nonEmpty) Some(tpl(mkSeq(tps map encodeType))) else None
            val rsubs = (subs zip up.subTypes(tpe)) map (p => transform(p._1, p._2))
            t.UnapplyPattern(ob map transform, rec, id, Seq(), rsubs).copiedFrom(pat)
          } else {
            super.transform(pat, tpe)
          }

        case s.LiteralPattern(ob, lit) =>
          if (isObject(tpe lub lit.getType)) {
            unapplier(lit.getType, transform(pat, lit.getType))
          } else {
            super.transform(pat, tpe)
          }
      }
    }

    private[this] object Scope {
      def empty(implicit symbols: s.Symbols) = new Scope(
        Map.empty,
        Map.empty,
        new DiGraph[s.FunAbstraction, SimpleEdge[s.FunAbstraction]]
      )
    }

    private[this] def transformFunction(fd: s.FunAbstraction)(implicit scope: Scope): t.FunAbstraction = {
      val scope0 = scope

      if (!(scope rewrite fd.id)) {
        fd.to(t)(
          fd.id,
          fd.tparams map (scope.transform(_)),
          fd.params map (scope.transform(_)),
          scope.transform(fd.returnType),
          scope.transform(fd.fullBody),
          fd.flags map (scope.transform(_))
        )
      } else {
        implicit val scope = scope0 in fd.id
        val tparamParams = fd.tparams map (tpd => scope.tparams(tpd.tp).asInstanceOf[Variable].toVal)

        val tparamConds = fd.tparams.foldLeft(Seq[Expr]()) { case (conds, tpd) =>
          val v = scope.tparams(tpd.tp)
          val s.TypeBounds(lowerBound, upperBound) = tpd.tp.bounds
          conds ++ Seq(
            if (lowerBound != s.NothingType()) subtypeOf(encodeType(lowerBound), v) else E(true),
            if (upperBound != s.AnyType()) subtypeOf(v, encodeType(upperBound)) else E(true)
          )
        }

        val newParams = fd.params.map(scope.transform(_))

        val paramConds = (newParams zip fd.params.map(_.tpe)).map { case (vd, tpe) =>
          if (!isObject(tpe)) t.BooleanLiteral(true)
          else instanceOf(vd.toVariable, encodeType(tpe))
        }

        val returnType = scope.transform(fd.returnType)

        val (specs, body) = s.exprOps.deconstructSpecs(fd.fullBody)(scope.symbols)

        val newSpecs = specs.map {
          case s.exprOps.Precondition(pre) =>
            val tpre = scope.transform(pre)
            t.exprOps.Precondition(t.andJoin(tparamConds ++ paramConds) match {
              case cond if cond != BooleanLiteral(true) =>
                t.and(t.Annotated(cond, Seq(t.Unchecked)).copiedFrom(fd), tpre).copiedFrom(pre)
              case _ =>
                tpre
            })

          case s.exprOps.Postcondition(post) =>
            val Lambda(Seq(res), body) = scope.transform(post)
            t.exprOps.Postcondition(t.Lambda(Seq(res), and(if (isObject(fd.returnType)) {
              t.Annotated(
                instanceOf(res.toVariable, encodeType(fd.returnType).copiedFrom(fd)).copiedFrom(fd),
                Seq(t.Unchecked)
              ).copiedFrom(fd)
            } else {
              E(true).copiedFrom(post)
            }, body).copiedFrom(post)).copiedFrom(post))

          case spec => spec.map(t)(scope.transform)
        }

        val newBody = body.map(e => scope.transform(e, fd.returnType))

        fd.to(t)(
          fd.id,
          Seq(),
          tparamParams ++ newParams,
          returnType,
          t.exprOps.reconstructSpecs(newSpecs, newBody, returnType),
          fd.flags map scope.transform
        )
      }
    }

    private[this] val baseScope = Scope.empty withFunctions symbols.functions.values.map(s.Outer(_)).toSeq

    def transform(fd: s.FunDef): t.FunDef = transformFunction(s.Outer(fd))(baseScope).toFun

    def transform(sort: s.ADTSort): t.ADTSort = baseScope.transform(sort)

    def functions: Seq[t.FunDef] =
      Seq(typeFunction) ++
      symbols.classes.values.flatMap(cd => constructor(cd.id) +: cd.fields.map(vd => field(cd.id, vd.id))) ++
      Seq(subtypeFunction, instanceFunction) ++
      unapplyFunctions ++
      Seq(wrapFunction, unwrapFunction) ++
      OptionSort.functions

    def sorts: Seq[t.ADTSort] =
      Seq(seqSort, tpeSort, objSort) ++
      OptionSort.sorts
  }

  override protected def transformSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    super.transformSymbols(context, symbols).withFunctions(context.functions).withSorts(context.sorts)
  }

  override protected def transformFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected def transformSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)

  // Classes are simply dropped by this extraction phase
  override protected type ClassResult = Unit
  override protected def transformClass(context: TransformerContext, symbols: s.Symbols): ClassResult = ()
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[Unit]): t.Symbols = symbols
}

object TypeEncoding {
  def apply(ts: Trees, tt: imperative.Trees)(prev: ExtractionPhase { val t: ts.type }): ExtractionPhase {
    val s: ts.type
    val t: tt.type
  } = new {
    override val s: ts.type = ts
    override val t: tt.type = tt
  } with TypeEncoding {
    override protected val previous: prev.type = prev
  }
}
