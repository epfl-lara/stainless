/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._
import scala.collection.mutable.{Map => MutableMap}

trait TypeEncoding extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {
    import t.{forall => _, _}
    import t.dsl._
    import s.TypeParameterWrapper

    def encodeName(s: String): String = s.replace("[", "<").replace("]", ">")

    implicit class TypeWrapper(tpe: s.Type) {
      def lub(that: s.Type): s.Type = syms.leastUpperBound(tpe, that)
      def glb(that: s.Type): s.Type = syms.greatestLowerBound(tpe, that)
    }


    /* ====================================
     *             REF-TYPES ADT
     * ==================================== */

    val objSort = mkSort(FreshIdentifier("Object"))()(_ => Seq(
      (FreshIdentifier("Object"), Seq("ptr" :: IntegerType()))
    ))
    val obj = T(objSort.id)()
    val Seq(objCons) = objSort.constructors
    val Seq(objPtr) = objCons.fields.map(_.id)


    /* ====================================
     *        TYPE ADT IDENTIFIERS
     * ==================================== */

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
    val seq  = T(seqID)()

    val head = FreshIdentifier("head")
    val tail = FreshIdentifier("tail")

    val seqSort  = mkSort(seqID)()(_ => Seq(
      (FreshIdentifier("Cons"), Seq(ValDef(head, tpe), ValDef(tail, seq))),
      (FreshIdentifier("Nil"), Seq())
    ))
    val Seq(cons, nil) = seqSort.constructors

    def mkSeq(es: Seq[Expr]): Expr = es.foldRight(nil())((h, t) => cons(h, t))
    def seqAt(s: Expr, i: Int): Expr =
      if (i <= 0) Assume(s is cons, s.getField(head))
      else Assume(s is cons, seqAt(s.getField(tail), i - 1))


    /* ====================================
     *           TYPE ADTS
     * ==================================== */

    val tpeSort = mkSort(tpeID)()(_ => Seq(
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

    val Seq(bot, top, ref, cls, adt, arr, set, bag, map, fun, tpl, bool, int, bv, char, unit, real, str) =
      tpeSort.constructors

    val Seq(refPred) = ref.fields.map(_.id)
    val Seq(clsPtr, clsTps) = cls.fields.map(_.id)
    val Seq(adtPtr, adtTps) = adt.fields.map(_.id)
    val Seq(arrBase) = arr.fields.map(_.id)
    val Seq(setBase) = set.fields.map(_.id)
    val Seq(bagBase) = bag.fields.map(_.id)
    val Seq(mapFrom, mapTo) = map.fields.map(_.id)
    val Seq(funFrom, funTo) = fun.fields.map(_.id)
    val Seq(tplTps) = tpl.fields.map(_.id)
    val Seq(bvSize) = bv.fields.map(_.id)


    /* ====================================
     *      BOXING/UNBOXING FUNCTIONS
     * ==================================== */

    val unwrapFunction: t.FunDef =
      mkFunDef(FreshIdentifier("unwrap"), Unchecked)("T") { case Seq(aT) =>
        (Seq("x" :: obj), aT, { case Seq(x) => choose("res" :: aT)(_ => E(true)) })
      }

    def unwrap(e: t.Expr, expected: t.Type): t.Expr = {
      if (expected == obj) e
      else FunctionInvocation(unwrapFunction.id, Seq(expected), Seq(e)).copiedFrom(e)
    }

    val wrapFunction: t.FunDef =
      mkFunDef(FreshIdentifier("wrap"), Unchecked)("T") { case Seq(aT) =>
        (Seq("x" :: aT), obj, { case Seq(x) => choose("res" :: obj)(res => unwrap(res, aT) === x) })
      }

    def wrap(e: t.Expr, tpe: t.Type): t.Expr = {
      if (tpe == obj) e
      else FunctionInvocation(wrapFunction.id, Seq(tpe), Seq(e)).copiedFrom(e)
    }


    /* ====================================
     *  SUBTYPING/INSTANCEOF FUNCTION IDS
     * ==================================== */

    val subtypeID = FreshIdentifier("isSubtypeOf")
    def subtypeOf(e1: Expr, e2: Expr) = FunctionInvocation(subtypeID, Seq(), Seq(e1, e2))

    val instanceID = FreshIdentifier("isInstanceOf")
    def instanceOf(e1: Expr, e2: Expr) = FunctionInvocation(instanceID, Seq(), Seq(e1, e2))


    /* ====================================
     *         SUBTYPING FUNCTION
     * ==================================== */

    class TypeScope protected(val tparams: Map[s.TypeParameter, t.Expr]) extends TransformerWithType {
      val s: self.s.type = self.s
      val t: self.t.type = self.t
      val symbols: syms.type = syms

      override def transform(tp: s.Type): t.Type = tp match {
        case s.NothingType() | s.AnyType() | (_: s.ClassType) | (_: s.RefinementType) => obj
        case tp: s.TypeParameter if tparams contains tp => obj
        case (_: s.TypeBounds) | (_: s.UnionType) | (_: s.IntersectionType) =>
          throw MissformedStainlessCode(tp, s"Type $tp should never occur in input.")
        case _ => super.transform(tp)
      }

      // This transformer should be used instead of `transform` to transform types obtained
      // through `getType` (these types aren't annotated in the program).
      private[this] val getTypeTransformer = new oo.TreeTransformer {
        val s: self.s.type = self.s
        val t: self.t.type = self.t

        override def transform(tpe: s.Type): t.Type = tpe match {
          case s.NothingType() | s.AnyType() | (_: s.ClassType) => obj
          case tp: s.TypeParameter if tparams contains tp => obj
          case (_: s.TypeBounds) | (_: s.UnionType) | (_: s.IntersectionType) | (_: s.RefinementType) =>
            transform(syms.widen(tpe))
          case _ => super.transform(tpe)
        }
      }

      def transformGetType(e: s.Expr): t.Type = getTypeTransformer.transform(e.getType(symbols))
    }

    object TypeScope {
      def empty = new TypeScope(Map.empty)

      def apply(cd: s.ClassDef, tpe: Expr): TypeScope = {
        val clsParams = cd.tparams.indices.map(i => seqAt(tpe.getField(clsTps), i))
        val newTParams = (cd.tparams.map(_.tp) zip clsParams).toMap
        new TypeScope(newTParams)
      }

      def apply(d: s.ADTSort, tpe: Expr): TypeScope = {
        val adtParams = d.tparams.indices.map(i => seqAt(tpe.getField(adtTps), i))
        val newTParams = (d.tparams.map(_.tp) zip adtParams).toMap
        new TypeScope(newTParams)
      }

      def apply(pairs: Traversable[(s.TypeParameter, t.Expr)]): TypeScope = new TypeScope(pairs.toMap)
    }

    def encodeType(tpe: s.Type)(implicit scope: TypeScope): t.Expr = tpe match {
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

    val subtypeFunction = mkFunDef(subtypeID, Unchecked)()(_ => (
      Seq("tp1" :: tpe, "tp2" :: tpe), BooleanType(), {
        case Seq(tp1, tp2) => Seq(
          (tp2 is top) -> E(true),
          (tp1 is bot) -> E(true),
          (tp1 is ref) -> forall("x" :: obj)(x => tp1.getField(refPred)(x) ==> instanceOf(x, tp2)),
          (tp2 is ref) -> forall("x" :: obj)(x => instanceOf(x, tp1) ==> tp2.getField(refPred)(x)),
          (tp1 is cls) -> (
            (tp2 is cls) &&
            syms.classes.values.foldRight(
              IfExpr(andJoin(syms.classes.values.filter(_.flags contains s.IsSealed).toSeq.map {
                cd => !(tp2.getField(clsPtr) === IntegerLiteral(cd.id.globalId))
              }), choose("res" :: BooleanType())(_ => E(true)), E(false)): Expr
            ) {
              case (cd, elze) => IfExpr(
                tp1.getField(clsPtr) === IntegerLiteral(cd.id.globalId),
                (
                  tp2.getField(clsPtr) === IntegerLiteral(cd.id.globalId) && {
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
                      case Seq() => E(true)
                    }

                    rec(cd.typeArgs, tp1.getField(clsTps), tp2.getField(clsTps))
                  }
                ) || (
                  orJoin(cd.parents.map(ct => subtypeOf(encodeType(ct)(TypeScope(cd, tp1)), tp2)))
                ),
                elze
              )
            }
          ),
          (tp1 is adt) -> (
            (tp2 is adt) &&
            syms.sorts.values.foldRight(E(false)) {
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

    def isObject(tpe: s.Type)(implicit scope: TypeScope): Boolean = tpe match {
      case _: s.ClassType => true
      case s.NothingType() | s.AnyType() => true
      case (_: s.UnionType) | (_: s.IntersectionType) => true
      case tp: s.TypeParameter if scope.tparams contains tp => true
      case _ => false
    }

    def isSimple(tpe: s.Type)(implicit scope: TypeScope): Boolean = !s.typeOps.exists(isObject)(tpe)


    /* ====================================
     *          GET-TYPE FUNCTION
     * ==================================== */

    val typeField = FreshIdentifier("getType")
    val typeFunction = mkFunDef(typeField, Unchecked)()(_ => (
      Seq("e" :: obj), tpe, { case Seq(e) => choose("res" :: tpe)(_ => E(true)) }))

    val typeOf = (e: Expr) => FunctionInvocation(typeField, Seq(), Seq(e))


    /* ====================================
     *         INSTANCEOF FUNCTION
     * ==================================== */

    val instanceFunction = mkFunDef(instanceID, Unchecked)()(_ => (
      Seq("e" :: obj, "tp2" :: tpe), BooleanType(), {
        case Seq(e, tp2) => let("tp1" :: tpe, typeOf(e))(tp1 => Seq(
          (tp2 is bot) -> E(false),
          (tp2 is top) -> E(true),
          (tp2 is ref) -> tp1.getField(refPred)(e),
          (tp2 is cls) -> (
            (tp1 is cls) &&
            andJoin(syms.classes.values.toSeq.filter(_.flags contains s.IsAbstract).map {
              cd => !(tp1.getField(clsPtr) === IntegerLiteral(cd.id.globalId))
            }) &&
            subtypeOf(tp1, tp2)
          )
        ).foldRight(subtypeOf(tp1, tp2): Expr) {
          case ((cond, thenn), elze) => IfExpr(cond, thenn, elze)
        }).copiedFrom(e)
      }))


    /* ====================================
     *     REF-TYPE FIELDS & WRAPPERS
     * ==================================== */

    val classFields = syms.classes.values.flatMap { cd =>
      cd.fields.map { vd =>
        val id = vd.id.freshen
        val arg = ValDef(FreshIdentifier("e"), obj)
        implicit val scope = TypeScope(cd, typeOf(arg.toVariable))

        val resTpe = scope.transform(vd.tpe)
        val fieldFunction = mkFunDef(id, Unchecked)()(_ => (Seq(arg), resTpe, {
          case Seq(_) => choose("res" :: resTpe) { res =>
            if (isObject(vd.tpe)) {
              instanceOf(res, encodeType(vd.tpe))
            } else {
              E(true)
            }
          }
        }))

        vd.id -> fieldFunction
      }
    }.toMap

    def getField(e: t.Expr, id: Identifier): t.Expr = FunctionInvocation(classFields(id).id, Seq(), Seq(e))

    val classConstructors = syms.classes.values.map { cd =>
      val ct = s.ClassType(cd.id, cd.typeArgs)
      val tparamParams = cd.tparams.map(tpd => t.ValDef(tpd.id.freshen, tpe).copiedFrom(tpd))
      implicit val scope = TypeScope(cd.typeArgs zip tparamParams.map(_.toVariable))
      val paramParams = cd.fields.map(vd => t.ValDef(vd.id.freshen, scope.transform(vd.tpe)))

      cd.id -> mkFunDef(cd.id.freshen, Unchecked)()(_ => (
        tparamParams ++ paramParams, obj, { case args =>
          choose(ValDef(FreshIdentifier("ptr", true), obj, Set(Unchecked))) { res =>
            typeOf(res) === encodeType(ct) &&
            andJoin((cd.fields zip args.drop(tparamParams.size)).map(p => getField(res, p._1.id) === p._2))
          }
        }
      ))
    }.toMap

    val fieldFunctions: Seq[t.FunDef] = typeFunction +: (classFields.values.toSeq ++ classConstructors.values)

    val unificationCache: MutableMap[(t.Type, t.Type), t.FunDef] = MutableMap.empty
    def unificationFunctions: Seq[t.FunDef] = unificationCache.values.toSeq

    /* Transforms `e` of type `tpe` into an expression of type `expected`.
     * Note that neither `tpe` nor `expected` will contain type parameters so we can maintain a global
     * cache of the ADT unification functions. */
    def unifyTypes(e: t.Expr, tpe: t.Type, expected: t.Type): t.Expr = {

      def containsObj(tpe: t.Type): Boolean = t.typeOps.exists { case `obj` => true case _ => false } (tpe)

      val unifications: MutableMap[(t.Type, t.Type), Identifier] = MutableMap.empty

      def rec(e: t.Expr, lo: t.Type, hi: t.Type): t.Expr = (lo, hi) match {
        case (t1, t2) if t1 == t2 => e
        case (t1, t2) if !containsObj(t1) && !containsObj(t2) => e
        case (`obj`, t2) => unwrap(e, t2)
        case (t1, `obj`) => wrap(e, t1)

        case (FunctionType(from1, to1), FunctionType(from2, to2)) => e match {
          case Lambda(args, body) =>
            val newArgs = (args zip from2).map { case (vd, tpe) => vd.copy(tpe = tpe) }
            val argMap = ((from1 zip from2) zip args).map { case ((tp1, tp2), vd) =>
              vd.toVariable -> rec(vd.copy(tpe = tp2).toVariable, tp2, tp1)
            }.toMap
            val newBody = rec(exprOps.replaceFromSymbols(argMap, body), to1, to2)
            Lambda(newArgs, newBody).copiedFrom(e)
          case _ =>
            val newArgs = from2.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
            val appArgs = ((from1 zip from2) zip newArgs).map { case ((tp1, tp2), vd) =>
              rec(vd.toVariable, tp2, tp1)
            }
            val newBody = rec(Application(e, appArgs).copiedFrom(e), to1, to2)
            Lambda(newArgs, newBody).copiedFrom(e)
        }

        case (TupleType(tps1), TupleType(tps2)) => e match {
          case Tuple(es) => Tuple(((tps1 zip tps2) zip es).map {
            case ((tp1, tp2), e) => rec(e, tp1, tp2)
          })
          case _ => Tuple((tps1 zip tps2).zipWithIndex.map {
            case ((tp1, tp2), i) => rec(TupleSelect(e, i + 1), tp1, tp2)
          })
        }

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

          FunctionInvocation(id, Seq(), Seq(e))

        case (ArrayType(b1), ArrayType(b2)) => choose(ValDef(FreshIdentifier("res"), hi, Set(Unchecked))) {
          res => forall("i" :: Int32Type())(i => rec(ArraySelect(e, i), b1, b2) === ArraySelect(res, i))
        }

        case (SetType(b1), SetType(b2)) => choose(ValDef(FreshIdentifier("res"), hi, Set(Unchecked))) {
          res => forall("x" :: b1)(x => ElementOfSet(x, e) === ElementOfSet(rec(x, b1, b2), res))
        }

        case (BagType(b1), BagType(b2)) => choose(ValDef(FreshIdentifier("res"), hi, Set(Unchecked))) {
          res => forall("x" :: b1)(x => MultiplicityInBag(x, e) === MultiplicityInBag(rec(x, b1, b2), res))
        }

        case (MapType(f1, t1), MapType(f2, t2)) => choose(ValDef(FreshIdentifier("res"), hi, Set(Unchecked))) {
          res => forall("x" :: f1)(x => rec(MapApply(e, x), t1, t2) === MapApply(res, rec(x, f1, f2)))
        }

        case _ => e
      }

      rec(e, tpe, expected)
    }


    /* ====================================
     *          UNAPPLY FUNCTIONS
     * ==================================== */

    val (option, some, none, isEmpty, get, optionSort, optionIsEmpty, optionGet) =
      syms.lookup.get[s.ADTSort]("stainless.lang.Option") match {
        case Some(sort) =>
          val some = sort.constructors.find(_.fields.nonEmpty).get
          val none = sort.constructors.find(_.fields.isEmpty).get
          val isEmpty = syms.lookup[s.FunDef]("stainless.lang.Option.isEmpty")
          val get = syms.lookup[s.FunDef]("stainless.lang.Option.get")
          (sort.id, some.id, none.id, isEmpty.id, get.id, None, None, None)
        case None =>
          val Seq(option, some, none, isEmpty, get) =
            Seq("Option", "Some", "None", "Option.isEmpty", "Option.get")
              .map(name => ast.SymbolIdentifier("stainless.lang" + name))
          val value = FreshIdentifier("value")
          (option, some, none, isEmpty, get,
            Some(mkSort(option)("A") { case Seq(aT) => Seq((some, Seq(t.ValDef(value, aT))), (none, Seq())) }),
            Some(mkFunDef(isEmpty, t.Unchecked)("A") {
              case Seq(aT) => (Seq("x" :: T(option)(aT)), t.BooleanType(), { case Seq(v) => v is none })
            }),
            Some(mkFunDef(get, t.Unchecked)("A") {
              case Seq(aT) => (Seq("x" :: T(option)(aT)), aT, {
                case Seq(v) => t.Require(v is some, v.getField(value))
              })
            }))
      }

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

    val classUnapplierCache: MutableMap[Identifier, t.FunDef] = MutableMap.empty
    def classUnapplier(id: Identifier): Identifier = classUnapplierCache.getOrElseUpdate(id, {
      val cd = syms.getClass(id)
      val arg = t.ValDef(FreshIdentifier("x"), obj)
      implicit val scope = TypeScope(cd, typeOf(arg.toVariable))
      val tt = t.tupleTypeWrap(cd.fields.map(vd => if (isObject(vd.tpe)) obj else scope.transform(vd.tpe)))
      mkFunDef(FreshIdentifier(id.name), Unchecked, IsUnapply(isEmpty, get))() { _ =>
        (Seq("thiss" :: tpe, arg), T(option)(tt), { case Seq(thiss, x) =>
          if_ (instanceOf(x, thiss)) {
            C(some)(tt)(t.tupleWrap(cd.fields.map(vd => getField(x, vd.id))))
          } else_ {
            C(none)(tt)()
          }
        })
      }
    }).id

    def unapplyFunctions: Seq[t.FunDef] =
      Seq(unwrapUnapplierFunction, instanceUnapplierFunction) ++ classUnapplierCache.values


    /* ====================================
     *      FUNCTION TRANSFORMATION
     * ==================================== */

    abstract class FunInfo {
      val fun: s.FunAbstraction
      val outer: Option[Scope]
      def rewrite: Boolean
    }

    case class RewriteInfo(fun: s.FunAbstraction, outer: Option[Scope], tparams: Seq[t.ValDef])
      extends FunInfo { def rewrite = true }
    case class SimpleInfo(fun: s.FunAbstraction, outer: Option[Scope])
      extends FunInfo { def rewrite = false }

    class Scope private(
      functions: Map[Identifier, FunInfo],
      tparams: Map[s.TypeParameter, t.Expr],
      graph: DiGraph[s.FunAbstraction, SimpleEdge[s.FunAbstraction]]
    ) extends TypeScope(tparams) {
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
              (subs zip s.unwrapTupleType(up.getGet.returnType, subs.size)) foreach (p => traverse(p._1, p._2))

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
            case s.ClassType(_, _) => simple = false
            case s.RefinementType(_, _) => simple = false
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
          val fd = classConstructors(ct.id)
          val newArgs = (fd.params.drop(ct.tps.length) zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transformGetType(arg), vd.tpe)
          }

          t.FunctionInvocation(fd.id, Seq(), ct.tps.map(encodeType) ++ newArgs).copiedFrom(e)

        case s.ClassSelector(expr, id) =>
          getField(transform(expr), id).copiedFrom(e)

        case s.IsInstanceOf(expr, tpe) if isObject(expr.getType lub tpe) =>
          instanceOf(transform(expr), encodeType(tpe)).copiedFrom(e)

        case s.IsInstanceOf(expr, tpe) =>
          t.BooleanLiteral(isSubtypeOf(expr.getType, tpe)).copiedFrom(e)

        case s.AsInstanceOf(expr, tpe) if isObject(expr.getType lub tpe) =>
          val exprType = expr.getType
          val te = transform(expr)
          val check = subtypeOf(if (isObject(exprType)) typeOf(te) else encodeType(exprType), encodeType(tpe))
          val result = if (isObject(exprType) && !isObject(tpe)) unwrap(te, transform(tpe))
            else if (!isObject(exprType) && isObject(tpe)) wrap(te, transform(tpe))
            else te

          t.Assert(check, Some("Cast error"), result)

        case s.AsInstanceOf(expr, tpe) => transform(expr)

        case fi @ s.FunctionInvocation(id, tps, args) if scope rewrite id =>
          val fdScope = this in id
          val fd = getFunction(id)

          val newArgs = (fd.params zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transformGetType(arg), fdScope.transform(vd.tpe))
          } ++ tps.map(encodeType)

          unifyTypes(
            t.FunctionInvocation(id, Seq(), newArgs),
            fdScope.transform(fd.returnType),
            transform(fi.tfd.returnType)
          )

        case app @ s.ApplyLetRec(v, tparams, tps, args) if scope rewrite v.id =>
          val appScope = this in v.id
          val fun = functions(v.id).fun

          val newArgs = (fun.params zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transformGetType(arg), appScope.transform(vd.tpe))
          } ++ tps.map(encodeType)

          val vd @ t.ValDef(id, FunctionType(from, to), flags) = appScope.transform(v.toVal)
          val nvd = vd.copy(tpe = FunctionType(from ++ tparams.map(_ => tpe), to))

          unifyTypes(
            t.ApplyLetRec(nvd.toVariable, Seq(), Seq(), newArgs),
            appScope.transform(fun.returnType),
            transform(app.getType)
          )

        case app @ s.ApplyLetRec(v, tparams, tps, args) =>
          val appScope = functions(v.id).outer.get
          unifyTypes(t.ApplyLetRec(
            appScope.transform(v.toVal).toVariable,
            tparams map (appScope.transform(_).asInstanceOf[t.TypeParameter]),
            tps map transform,
            args map transform
          ).copiedFrom(e), transformGetType(app), transform(inType))

        case s.LetRec(fds, body) =>
          val funs = fds.map(fd => s.Inner(fd))
          val newScope = scope withFunctions funs
          val newFuns = funs.map(fun => transformFunction(fun)(newScope))
          val newBody = newScope.transform(body, inType)
          t.LetRec(newFuns.map(_.toLocal), newBody).copiedFrom(e)

        case e if !isObject(e.getType) && isObject(inType) =>
          unifyTypes(transform(e), transformGetType(e), transform(inType))

        case e if isObject(e.getType) && !isObject(inType) =>
          unifyTypes(transform(e), transformGetType(e), transform(inType))

        case _ => super.transform(e, inType)
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
          val id = classUnapplier(ct.id)
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
            val rsubs = (subs zip s.unwrapTupleType(up.getGet.returnType, subs.size)) map (p => transform(p._1, p._2))
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

    object Scope {
      def empty = new Scope(
        Map.empty,
        Map.empty,
        new DiGraph[s.FunAbstraction, SimpleEdge[s.FunAbstraction]]
      )
    }

    def transformFunction(fd: s.FunAbstraction)(implicit scope: Scope): t.FunAbstraction = {
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

        val (specs, body) = s.exprOps.deconstructSpecs(fd.fullBody)(syms)

        val newSpecs = specs.map {
          case s.exprOps.Precondition(pre) =>
            t.exprOps.Precondition(t.andJoin(
              (scope.transform(pre) +: tparamConds) ++ paramConds
            ))

          case s.exprOps.Postcondition(post) =>
            val Lambda(Seq(res), body) = scope.transform(post)
            t.exprOps.Postcondition(Lambda(Seq(res), and(body, if (isObject(fd.returnType)) {
              instanceOf(res.toVariable, encodeType(fd.returnType).copiedFrom(post)).copiedFrom(post)
            } else {
              E(true).copiedFrom(post)
            }).copiedFrom(post)).copiedFrom(post))

          case spec => spec.map(t)(scope.transform)
        }

        val newBody = body.map(e => scope.transform(e, fd.returnType))

        fd.to(t)(
          fd.id,
          Seq.empty,
          newParams ++ tparamParams,
          returnType,
          t.exprOps.reconstructSpecs(newSpecs, newBody, returnType),
          fd.flags map scope.transform
        )
      }
    }

    val symbolFuns = syms.functions.values.map(s.Outer(_)).toSeq
    val baseScope = Scope.empty withFunctions symbolFuns

    val functions: Seq[t.FunDef] = symbolFuns.map(fd => transformFunction(fd)(baseScope).toFun)

    val sorts: Seq[t.ADTSort] = syms.sorts.values.map(d => baseScope.transform(d)).toSeq

    val newSymbols = NoSymbols
      .withFunctions(
        Seq(subtypeFunction, instanceFunction) ++ 
        unapplyFunctions ++
        fieldFunctions ++
        Seq(wrapFunction, unwrapFunction) ++
        unificationFunctions ++
        functions)
      .withSorts(
        Seq(seqSort, tpeSort, objSort) ++
        optionSort ++ // Note that if stainless.lang.Option was already in sorts, this is a Noop
        sorts)

    for (fd <- newSymbols.functions.values) {
      if (!newSymbols.isSubtypeOf(fd.fullBody.getType(newSymbols), fd.returnType)) {
        println(fd)
        println(newSymbols.explainTyping(fd.fullBody)(PrinterOptions(printUniqueIds = true, symbols = Some(newSymbols))))
      }
    }

    def inlineChecks(e: Expr): Expr = {
      import newSymbols._
      import exprOps._

      // TODO @nv: implement some controlled fixpoint here.
      //           We should be able to call ourselves recursively on the output of simplification
      //           in most cases, but some care has to be taken to terminate.
      exprOps.postMap {
        case fi @ FunctionInvocation(`subtypeID`, Seq(), Seq(
          ADT(tpl.id, Seq(), Seq(ADTSelector(_, `tail`))),
          ADT(tpl.id, Seq(), Seq(ADTSelector(_, `tail`)))
        )) => None

        case fi @ FunctionInvocation(`subtypeID`, Seq(), Seq(
          ADT(fun.id, Seq(), Seq(ADTSelector(_, `tail`), _)),
          ADT(fun.id, Seq(), Seq(ADTSelector(_, `tail`), _))
        )) => None

        case fi @ FunctionInvocation(`subtypeID`, Seq(), args @ (Seq(_: ADT, _) | Seq(_, _: ADT))) =>
          val tfd = fi.tfd
          val body = freshenLocals(tfd.withParamSubst(args, tfd.fullBody))
          val simp = newSymbols.simplifyExpr(body)(inox.solvers.PurityOptions.assumeChecked)
          if (simp != body) Some(simp) else None

        case fi @ FunctionInvocation(`instanceID`, Seq(), args @ Seq(_, _: ADT)) =>
          val tfd = fi.tfd
          val body = freshenLocals(tfd.withParamSubst(args, tfd.fullBody))
          val simp = newSymbols.simplifyExpr(body)(inox.solvers.PurityOptions.assumeChecked)
          if (simp != body) Some(simp) else None
        case _ => None
      } (e)
    }

    val finalSymbols = NoSymbols
      .withFunctions(newSymbols.functions.values.toSeq.map(fd => fd.copy(fullBody = inlineChecks(fd.fullBody))))
      .withSorts(newSymbols.sorts.values.toSeq)

    for (fd <- finalSymbols.functions.values) {
      if (!finalSymbols.isSubtypeOf(fd.fullBody.getType(finalSymbols), fd.returnType)) {
        println(fd)
        println(finalSymbols.explainTyping(fd.fullBody)(PrinterOptions(printUniqueIds = true, symbols = Some(finalSymbols))))
      }
    }

    finalSymbols
  }
}
