/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._
import scala.collection.mutable.{Map => MutableMap}

trait TypeEncoding extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: holes.Trees

  def transform(symbols: s.Symbols): t.Symbols = {
    import t.{forall => _, _}
    import t.dsl._
    import s.TypeParameterWrapper

    def encodeName(s: String): String = s.replace("[", "<").replace("]", ">")

    implicit class TypeWrapper(tpe: s.Type) {
      def lub(that: s.Type): s.Type = symbols.leastUpperBound(tpe, that)
      def glb(that: s.Type): s.Type = symbols.greatestLowerBound(tpe, that)
    }

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

    def mkSeq(es: Seq[Expr]): Expr = es.foldRight(nil())((h, t) => cons(h, t))
    def seqAt(s: Expr, i: Int): Expr =
      if (i <= 0) Assume(s is cons, s.getField(head))
      else Assume(s is cons, seqAt(s.getField(tail), i - 1))

    val seqSort  = mkSort(seqID)()(_ => Seq(
      (FreshIdentifier("Cons"), Seq(ValDef(head, tpe), ValDef(tail, seq))),
      (FreshIdentifier("Nil"), Seq())
    ))
    val Seq(cons, nil) = seqSort.constructors


    /* ====================================
     *           TYPE ADTS
     * ==================================== */

    val tpeSort = mkSort(tpeID)()(_ => Seq(
      /* Bottom type, corresponds to Scala's {{{Nothing}}} */
      (FreshIdentifier("Bot"), Seq()),

      /* Top type, corresponds to Scala's {{{Any}}} */
      (FreshIdentifier("Top"), Seq()),

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

    val Seq(bot, top, cls, adt, arr, set, bag, map, fun, tpl, bool, int, bv, char, unit, real, str) =
      tpeSort.constructors

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
     *             REF-TYPES ADT
     * ==================================== */

    val objSort = mkSort(FreshIdentifier("Object"))()(_ => Seq(
      (FreshIdentifier("Object"), Seq("ptr" :: IntegerType()))
    ))
    val obj = T(objSort.id)()
    val Seq(objCons) = objSort.constructors
    val Seq(objPtr) = objCons.fields.map(_.id)


    /* ====================================
     *         SUBTYPING FUNCTION
     * ==================================== */

    class TypeScope protected(val tparams: Map[s.TypeParameter, t.Expr]) extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(tp: s.Type): t.Type = tp match {
        case s.NothingType() | s.AnyType() | (_: s.ClassType) => obj
        case tp: s.TypeParameter if tparams contains tp => obj
        case (_: s.TypeBounds) | (_: s.UnionType) | (_: s.IntersectionType) =>
          throw MissformedStainlessCode(tp, "Unexpected type " + tp)
        case _ => super.transform(tp)
      }
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

    val subtypeID = FreshIdentifier("isSubtypeOf")
    val subtypeOf = (e1: Expr, e2: Expr) => FunctionInvocation(subtypeID, Seq(), Seq(e1, e2))

    val subtypeFunction = mkFunDef(subtypeID, Unchecked)()(_ => (
      Seq("tp1" :: tpe, "tp2" :: tpe), BooleanType(), {
        case Seq(tp1, tp2) => Seq(
          (tp2 is top) -> E(true),
          (tp1 is bot) -> E(true),
          (tp1 is cls) -> (
            (tp2 is cls) &&
            symbols.classes.values.foldRight(
              IfExpr(andJoin(symbols.classes.values.filter(_.flags contains s.IsSealed).toSeq.map {
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

    val instanceID = FreshIdentifier("isInstanceOf")
    val instanceOf = (e1: Expr, e2: Expr) => FunctionInvocation(instanceID, Seq(), Seq(e1, e2))

    val instanceFunction = mkFunDef(instanceID, Unchecked)()(_ => (
      Seq("e" :: obj, "tp2" :: tpe), BooleanType(), {
        case Seq(e, tp2) => let("tp1" :: tpe, typeOf(e))(tp1 => Seq(
          (tp2 is bot) -> E(false),
          (tp2 is top) -> E(true),
          (tp2 is cls) -> (
            (tp1 is cls) &&
            andJoin(symbols.classes.values.toSeq.filter(_.flags contains s.IsAbstract).map {
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

    val classFields = symbols.classes.values.flatMap { cd =>
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

    val classConstructors = symbols.classes.values.map { cd =>
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

    val unwrapCache: MutableMap[t.Type, t.FunDef] = MutableMap.empty
    def unwrapFunctions: Seq[t.FunDef] = unwrapCache.values.toSeq

    def unwrap(e: t.Expr, expected: t.Type): t.Expr = {
      val fd = unwrapCache.getOrElseUpdate(expected, {
        mkFunDef(FreshIdentifier(encodeName("unwrap" + expected)), Unchecked)()(_ => (
          Seq("x" :: obj), expected, { case Seq(x) => choose("res" :: expected)(_ => E(true)) }
        ))
      })
      FunctionInvocation(fd.id, Seq(), Seq(e)).copiedFrom(e)
    }

    val wrapCache: MutableMap[t.Type, t.FunDef] = MutableMap.empty
    def wrapFunctions: Seq[t.FunDef] = wrapCache.values.toSeq

    def wrap(e: t.Expr, tpe: t.Type): t.Expr = {
      val fd = wrapCache.getOrElseUpdate(tpe, {
        mkFunDef(FreshIdentifier(encodeName("wrap" + tpe)), Unchecked)()(_ => (
          Seq("x" :: tpe), obj, { case Seq(x) => choose("res" :: obj)(res => unwrap(res, tpe) === x) }
        ))
      })
      FunctionInvocation(fd.id, Seq(), Seq(e)).copiedFrom(e)
    }

    val unificationCache: MutableMap[(t.Type, t.Type), t.FunDef] = MutableMap.empty
    def unificationFunctions: Seq[t.FunDef] = unificationCache.values.toSeq

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

        case (tpe1 @ ADTType(id, tps1), tpe2 @ ADTType(_, tps2)) =>
          val sort: s.ADTSort = symbols.getSort(id)
          val id = unificationCache.get((tpe1, tpe2)) match {
            case Some(fd) => fd.id
            case None => unifications.get((tpe1, tpe2)) match {
              case Some(id) => id
              case None =>
                val id = FreshIdentifier(encodeName("unify_" + tpe1 + "_" + tpe2))
                unifications += (tpe1, tpe2) -> id
                unificationCache += (tpe1, tpe2) -> mkFunDef(id, Unchecked)()(_ => (
                  Seq("e" :: tpe1), tpe2, { case Seq(e) =>
                    val scope = TypeScope.empty
                    val typeArgs = sort.typeArgs.map(scope.transform)
                    val condRecons :+ ((_, last)) = sort.constructors.map { cons =>

                      val fields = cons.fields.map { vd =>
                        val ttpe = scope.transform(vd.tpe)
                        def instantiate(tps: Seq[Type]): Type = {
                          val tpMap = (typeArgs zip tps).toMap
                          typeOps.postMap {
                            case tp: TypeParameter => tpMap.get(tp)
                            case _ => None
                          } (ttpe)
                        }
                        rec(ADTSelector(e, vd.id).copiedFrom(e), instantiate(tps1), instantiate(tps2))
                      }

                      (IsConstructor(e, cons.id).copiedFrom(e), ADT(cons.id, tps2, fields).copiedFrom(e))
                    }

                    condRecons.foldRight(last: Expr) { case ((cond, e), elze) => IfExpr(cond, e, elze).copiedFrom(cond) }
                  }
                ))
                id
            }
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

    val (option, some, none, optionSort) = symbols.lookup.get[s.ADTSort]("stainless.lang.Option") match {
      case Some(sort) =>
        val some = sort.constructors.find(_.fields.nonEmpty).get
        val none = sort.constructors.find(_.fields.isEmpty).get
        (sort.id, some.id, none.id, None)
      case None =>
        val sort = mkSort(FreshIdentifier("Option"))("A") {
          case Seq(aT) => Seq(
            (FreshIdentifier("Some"), Seq(ValDef(FreshIdentifier("value"), aT))),
            (FreshIdentifier("None"), Seq())
          )
        }
        val Seq(some, none) = sort.constructors
        (sort.id, some.id, none.id, Some(sort))
    }

    val unapplyAdtCache: MutableMap[Identifier, t.FunDef] = MutableMap.empty
    def getAdtUnapply(id: Identifier): Identifier = unapplyAdtCache.get(id) match {
      case Some(fd) => fd.id
      case None =>
        val sort = symbols.getSort(id)
        val arg = t.ValDef(FreshIdentifier("x"), obj)
        implicit val scope = TypeScope(sort, typeOf(arg.toVariable))

        val tparams = sort.tparams.map(scope.transform)
        val tt = t.tupleTypeWrap(t.ADTType(sort.id, tparams.map(_.tp)) +: sort.tparams.map(_ => tpe))

        val fd = new t.FunDef(
          FreshIdentifier("unapply_" + id.name), tparams, Seq(arg), T(option)(tt),
          let("tpe" :: tpe, typeOf(arg.toVariable)) { tpe =>
            if_ (
              (tpe is adt) &&
              tpe.getField(adtPtr) === IntegerLiteral(sort.id.globalId)
            ) {
              C(some)(tt)(tupleWrap(
                unwrap(arg.toVariable, t.ADTType(sort.id, tparams.map(_.tp))) +:
                sort.typeArgs.indices.map(i => seqAt(tpe.getField(adtTps), i))
              ))
            } else_ {
              C(none)(tt)()
            }
          },
          Set(Unchecked)
        )

        unapplyAdtCache += id -> fd
        fd.id
    }

    val unapplyClassCache: MutableMap[Identifier, t.FunDef] = MutableMap.empty
    def getClassUnapply(id: Identifier): Identifier = unapplyClassCache.get(id) match {
      case Some(fd) => fd.id
      case None =>
        val cd = symbols.getClass(id)
        val arg = t.ValDef(FreshIdentifier("x"), obj)
        implicit val scope = TypeScope(cd, typeOf(arg.toVariable))
        val tt = t.tupleTypeWrap(
          cd.fields.map(vd => if (isSimple(vd.tpe)) scope.transform(vd.tpe) else obj) ++
          cd.tparams.map(_ => tpe)
        )

        val fd = mkFunDef(FreshIdentifier("unapply_" + id.name), Unchecked)()(_ => (
          Seq(arg), T(option)(tt), { case Seq(x) =>
            let("tpe" :: tpe, typeOf(x)) { tpe =>
              if_ (
                (tpe is cls) &&
                tpe.getField(clsPtr) === IntegerLiteral(id.globalId)
              ) {
                C(some)(tt)(tupleWrap(
                  cd.fields.map(vd => getField(x, vd.id)) ++
                  cd.tparams.indices.map(i => seqAt(tpe.getField(clsTps), i))
                ))
              } else_ {
                C(none)(tt)()
              }
            }
          }))
        unapplyClassCache += id -> fd
        fd.id
    }

    val unapplyTupleCache: MutableMap[Int, t.FunDef] = MutableMap.empty
    def getTupleUnapply(size: Int): Identifier = unapplyTupleCache.get(size) match {
      case Some(fd) => fd.id
      case None =>
        val arg = t.ValDef(FreshIdentifier("x"), obj)
        val tt = tupleTypeWrap(Seq.fill(size)(obj))
        implicit val scope = TypeScope.empty

        val fd = mkFunDef(FreshIdentifier("unapply_Tuple" + size), Unchecked)()(_ => (
          Seq(arg), T(option)(tt), { case Seq(x) =>
            let("tpe" :: tpe, typeOf(x)) { tpe =>
              if_ (
                (tpe is tpl) &&
                (1 to size).foldLeft((E(true), x: Expr)) { case ((e, x), _) =>
                  (e && (x is cons), x.getField(tail))
                }._1
              ) {
                C(some)(tt)(unwrap(x, tt))
              } else_ {
                C(none)(tt)()
              }
            }
          }))
        unapplyTupleCache += size -> fd
        fd.id
    }

    def unapplyFunctions: Seq[t.FunDef] =
      unapplyAdtCache.values.toSeq ++
      unapplyClassCache.values ++
      unapplyTupleCache.values


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
        import symbols._

        var simple: Boolean = true
        object traverser extends s.TreeTraverser {
          protected def traversePattern(in: s.Expr, pat: s.Pattern): Unit = pat match {
            case s.WildcardPattern(_) =>
            case s.InstanceOfPattern(_, tpe) if !isSimple(in.getType lub tpe) => simple = false
            case s.ClassPattern(_, _, _) => simple = false
            case s.ADTPattern(ob, id, tps, subs) =>
              val tcons = symbols.getConstructor(id, tps)
              if (!isSimple(in.getType lub s.ADTType(tcons.sort.id, tps))) simple = false
              else {
                (tcons.fields zip subs).foreach(p => traversePattern(adtSelector(in, p._1.id), p._2))
              }

            case s.TuplePattern(ob, subs) =>
              subs.zipWithIndex.foreach(p => traversePattern(tupleSelect(in, p._2 + 1, subs.size), p._1))

            case up @ s.UnapplyPattern(ob, id, tps, subs) =>
              (s.unwrapTuple(up.get(in), subs.size) zip subs) foreach (traversePattern _).tupled

            case s.LiteralPattern(_, lit) if !isSimple(in.getType lub lit.getType) => simple = false
            case _ =>
          }

          override def traverse(e: s.Expr): Unit = e match {
            case s.ClassConstructor(_, _) => simple = false
            case s.ClassSelector(_, _) => simple = false
            case s.MatchExpr(scrut, cases) => cases.foreach { case s.MatchCase(pat, _, _) => traversePattern(scrut, pat) }
            case s.IsInstanceOf(e, tpe) if !isSimple(e.getType lub tpe) => simple = false
            case s.AsInstanceOf(e, tpe) if !isSimple(e.getType lub tpe) => simple = false
            case _ => super.traverse(e)
          }

          override def traverse(tpe: s.Type): Unit = tpe match {
            case s.ClassType(_, _) => simple = false
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
            case s.UnapplyPattern(_, id, _, _) if functions contains id => Set(functions(id).fun)
            case s.UnapplyPattern(_, id, _, _) if funMap contains id => Set(funMap(id))
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

      override def transform(e: s.Expr): t.Expr = e match {
        case s.ClassConstructor(ct, args) =>
          val fd = classConstructors(ct.id)

          val newArgs = (fd.params.drop(ct.tps.length) zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transform(arg.getType), vd.tpe)
          }

          t.FunctionInvocation(fd.id, Seq(), ct.tps.map(encodeType) ++ newArgs)

        case s.ClassSelector(expr, id) =>
          getField(transform(expr), id)

        case s.IsInstanceOf(expr, tpe) if isObject(expr.getType lub tpe) =>
          instanceOf(transform(expr), encodeType(tpe))

        case s.AsInstanceOf(expr, tpe) if isObject(expr.getType lub tpe) =>
          val exprType = expr.getType
          val te = transform(expr)
          val check = subtypeOf(if (isObject(exprType)) typeOf(te) else encodeType(exprType), encodeType(tpe))
          val result = if (isObject(exprType) && !isObject(tpe)) unwrap(te, transform(tpe))
            else if (!isObject(exprType) && isObject(tpe)) wrap(te, transform(tpe))
            else te

          t.Assert(check, Some("Cast error"), result)

        case (_: s.ADTSelector | _: s.MapApply) if isObject(e.getType) =>
          let("res" :: obj, super.transform(e)) { res =>
            t.Assume(instanceOf(res, encodeType(e.getType)), res)
          }

        case fi @ s.FunctionInvocation(id, tps, args) if scope rewrite id =>
          val fdScope = this in id
          val fd = symbols.getFunction(id)

          val newArgs = (fd.params zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transform(arg.getType), fdScope.transform(vd.tpe))
          } ++ tps.map(encodeType)

          unifyTypes(
            t.FunctionInvocation(id, Seq(), newArgs),
            fdScope.transform(fd.returnType),
            transform(fi.getType)
          )

        case app @ s.ApplyLetRec(v, tparams, tps, args) if scope rewrite v.id =>
          val appScope = this in v.id
          val fun = functions(v.id).fun

          val newArgs = (fun.params zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transform(arg.getType), appScope.transform(vd.tpe))
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
          t.ApplyLetRec(
            appScope.transform(v.toVal).toVariable,
            tparams map (appScope.transform(_).asInstanceOf[t.TypeParameter]),
            tps map transform,
            args map transform
          ).copiedFrom(e)

        case s.MatchExpr(scrut, cases) =>
          val isObj = isObject(symbols.leastUpperBound(cases.map(_.rhs.getType)))
          t.MatchExpr(transform(scrut), for (cse <- cases) yield {
            val (newPattern, newGuard) = transformPattern(scrut, cse.pattern)
            val guard = t.andJoin(cse.optGuard.map(transform).toSeq ++ newGuard) match {
              case t.BooleanLiteral(true) => None
              case cond => Some(cond)
            }
            val trhs = transform(cse.rhs)
            val rhs = if (!isObj || isObject(cse.rhs.getType)) trhs else wrap(trhs, transform(cse.rhs.getType))
            t.MatchCase(newPattern, guard, rhs).copiedFrom(cse)
          }).copiedFrom(e)

        case s.LetRec(fds, body) =>
          val funs = fds.map(fd => s.Inner(fd))
          val newScope = scope withFunctions funs
          val newFuns = funs.map(fun => transformFunction(fun)(newScope))
          val newBody = newScope.transform(body)
          t.LetRec(newFuns.map(_.toLocal), newBody).copiedFrom(e)

        case s.IfExpr(cond, thenn, elze) if isObject(thenn.getType lub elze.getType) =>
          val tt = transform(thenn)
          val te = transform(elze)
          t.IfExpr(transform(cond),
            if (isObject(thenn.getType)) tt else wrap(tt, transform(thenn.getType)),
            if (isObject(elze.getType)) te else wrap(te, transform(elze.getType))
          ).copiedFrom(e)

        case _ => super.transform(e)
      }

      private def transformPattern(scrut: s.Expr, pattern: s.Pattern): (t.Pattern, Option[t.Expr]) = {
        import symbols.{transform => _, _}

        def typePattern(tp: s.Type, variance: Option[Boolean]): (t.Pattern, t.Expr) = {
          val vd = t.ValDef(FreshIdentifier("tp", true), tpe)
          val tpSub = t.WildcardPattern(Some(vd))
          val tpCond = variance match {
            case Some(true) => subtypeOf(vd.toVariable, encodeType(tp))
            case Some(false) => subtypeOf(encodeType(tp), vd.toVariable)
            case None => t.Equals(vd.toVariable, encodeType(tp))
          }
          (tpSub, tpCond)
        }

        def rec(in: s.Expr, pattern: s.Pattern): (t.Pattern, t.Expr) = pattern match {
          case s.WildcardPattern(ob) =>
            (t.WildcardPattern(ob map transform), t.BooleanLiteral(true))

          case s.InstanceOfPattern(ob, tpe) =>
            val cond = if (isObject(in.getType lub tpe)) {
              instanceOf(transform(ob.map(_.toVariable).getOrElse(in), encodeType(tpe)))
            } else {
              t.BooleanLiteral(true)
            }
            (t.WildcardPattern(ob map transform), cond)

          case s.ClassPattern(ob, ct, subs) =>
            val v = ob.map(_.toVariable).getOrElse(in)
            val (rsubs, rconds) = (
              (ct.tcd.fields zip subs).map(p => rec(s.ClassSelector(asInstOf(v, ct), p._1.id), p._2)) ++
              (ct.tcd.cd.typeArgs zip ct.tps).map { case (tp, tpe) => typePattern(tpe,
                if (tp.isCovariant) Some(true)
                else if (tp.isContravariant) Some(false)
                else None)
              }
            ).unzip
            (t.UnapplyPattern(ob map transform, getClassUnapply(ct.id), Seq.empty, rsubs), andJoin(rconds))

          case s.ADTPattern(ob, id, tps, subs) =>
            val tcons = symbols.getConstructor(id, tps)
            val tpe = s.ADTType(tcons.sort.id, tps)
            if (isObject(in.getType lub tpe)) {
              val v = s.Variable.fresh("v", tpe)
              val (rsub, rcond) = rec(v, s.ADTPattern(ob, id, tps, subs))
              val (tpSubs, tpConds) = tps.map(typePattern(_, None)).unzip
              (t.UnapplyPattern(Some(transform(v.toVal)), getAdtUnapply(id), tps map transform, rsub +: tpSubs), andJoin(rcond +: tpConds))
            } else {
              val v = ob.map(_.toVariable).getOrElse(in)
              val (rsubs, rconds) = (tcons.fields zip subs).map(p => rec(adtSelector(v, p._1.id), p._2)).unzip
              (t.ADTPattern(ob map transform, id, tps map transform, rsubs), t.andJoin(rconds))
            }

          case s.TuplePattern(ob, subs) =>
            val v = ob.map(_.toVariable).getOrElse(in)
            val rs = subs.zipWithIndex.map(p => rec(tupleSelect(v, p._2 + 1, subs.size), p._1))
            in.getType match {
              case s.TupleType(tps) if subs.size == tps.size =>
                (t.TuplePattern(ob map transform, rs.map(_._1)), t.andJoin(rs.map(_._2)))
              case _ =>
                val (rsubs, rconds) = rs.unzip
                (t.UnapplyPattern(ob map transform, getTupleUnapply(subs.size), Seq.empty, rsubs), andJoin(rconds))
            }

          case up @ s.UnapplyPattern(ob, id, tps, subs) =>
            val rs = (s.unwrapTuple(up.get(in), subs.size) zip subs) map (rec _).tupled
            if (!rewrite(id)) {
              (t.UnapplyPattern(ob map transform, id, tps map transform, rs.map(_._1)), t.andJoin(rs.map(_._2)))
            } else {
              (t.UnapplyPattern(ob map transform, id, Seq.empty, rs.map(_._1)), andJoin(rs.map(_._2)))
            }

          case s.LiteralPattern(ob, lit) =>
            if (isObject(in.getType lub lit.getType)) {
              val v = transform(ob.map(_.toVariable).getOrElse(in))
              (t.WildcardPattern(ob map transform), t.Equals(v, transform(lit)))
            } else {
              (t.LiteralPattern(ob map transform, transform(lit).asInstanceOf[Literal[_]]), t.BooleanLiteral(true))
            }
        }

        val (newPattern, cond) = rec(scrut, pattern)
        (newPattern, cond match {
          case t.BooleanLiteral(true) => None
          case _ => Some(cond)
        })
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

        val (specs, body) = s.exprOps.deconstructSpecs(fd.fullBody)(symbols)

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

        val newBody = body.map(scope.transform)

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

    val symbolFuns = symbols.functions.values.map(s.Outer(_)).toSeq
    val baseScope = Scope.empty withFunctions symbolFuns

    val functions: Seq[t.FunDef] = symbolFuns.map(fd => transformFunction(fd)(baseScope).toFun)

    val sorts: Seq[t.ADTSort] = symbols.sorts.values.map(d => baseScope.transform(d)).toSeq

    val newSymbols = NoSymbols
      .withFunctions(
        Seq(subtypeFunction, instanceFunction) ++ 
        unapplyFunctions ++
        fieldFunctions ++
        wrapFunctions ++
        unwrapFunctions ++
        unificationFunctions ++
        functions)
      .withSorts(
        Seq(seqSort, tpeSort, objSort) ++
        optionSort ++ // Note that if stainless.lang.Option was already in sorts, this is a Noop
        sorts)

    def inlineChecks(e: Expr): Expr = {
      import newSymbols._
      import exprOps._

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
          Some(inlineChecks(simplifyByConstructors(body)))

        case fi @ FunctionInvocation(`instanceID`, Seq(), args @ Seq(_, _: ADT)) =>
          val tfd = fi.tfd
          val body = freshenLocals(tfd.withParamSubst(args, tfd.fullBody))
          Some(inlineChecks(simplifyByConstructors(body)))
        case _ => None
      } (e)
    }

    val finalSymbols = NoSymbols
      .withFunctions(newSymbols.functions.values.toSeq.map(fd => fd.copy(fullBody = inlineChecks(fd.fullBody))))
      .withSorts(newSymbols.sorts.values.toSeq)

    for (fd <- finalSymbols.functions.values) {
      if (!finalSymbols.isSubtypeOf(fd.fullBody.getType(finalSymbols), fd.returnType)) {
        println(fd)
        println(finalSymbols.explainTyping(fd.fullBody)(PrinterOptions()))
      }
    }

    finalSymbols
  }
}
