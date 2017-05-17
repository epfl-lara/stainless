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

    def encodeName(s: String): String = s.replace("[", "<").replace("]", ">")

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
    def seqAt(s: Expr, i: Int): Expr =
      if (i <= 0) Assume(s.isInstOf(cons), s.asInstOf(cons).getField(head))
      else Assume(s.isInstOf(cons), seqAt(s.asInstOf(cons).getField(tail), i - 1))

    val seqSort  = mkSort(seqID)()(Seq(consID, nilID))
    val consCons = mkConstructor(consID)()(Some(seqID))(_ => Seq(ValDef(head, tpe), ValDef(tail, seq)))
    val nilCons  = mkConstructor(nilID)()(Some(seqID))(_ => Seq())


    /* ====================================
     *           TYPE ADTS
     * ==================================== */

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
    val tpl = T(tplID)()

    /* Function type, corresponds to {{{(From1,...,FromN) => To}}} in Scala */
    val funID = FreshIdentifier("Function")
    val funFrom = FreshIdentifier("from") // `from` field in `(from1,...,fromN) => to` type
    val funTo   = FreshIdentifier("to")   // `to`   field in `(from1,...,fromN) => to` type
    val funCons = mkConstructor(funID)()(Some(tpeID))(_ => Seq(ValDef(funFrom, seq), ValDef(funTo, tpe)))
    val fun = T(funID)()

    /* Boolean type, corresponds to {{{Boolean}}} in Scala */
    val boolID = FreshIdentifier("Boolean")
    val boolCons = mkConstructor(boolID)()(Some(tpeID))(_ => Seq())
    val bool = T(boolID)()

    /* Integer type, corresponds to {{{BigInt}}} in Scala */
    val intID = FreshIdentifier("Integer")
    val intCons = mkConstructor(intID)()(Some(tpeID))(_ => Seq())
    val int = T(intID)()

    /* Bitvector type, corresponds to {{{Int}}}, {{{Short}}}, {{{Byte}}}, {{{Char}}}, ... in Scala */
    val bvID = FreshIdentifier("Bitvector")
    val bvSize = FreshIdentifier("size")
    val bvCons = mkConstructor(bvID)()(Some(tpeID))(_ => Seq(ValDef(bvSize, IntegerType)))
    val bv = T(bvID)()

    /* Character type, corresponds to {{{Char}}} in Scala */
    val charID = FreshIdentifier("Char")
    val charCons = mkConstructor(charID)()(Some(tpeID))(_ => Seq())
    val char = T(charID)()

    /* Unit type, corresponds to {{{Unit}}} in Scala */
    val unitID = FreshIdentifier("Unit")
    val unitCons = mkConstructor(unitID)()(Some(tpeID))(_ => Seq())
    val unit = T(unitID)()

    /* Unbounded real type */
    val realID = FreshIdentifier("Real")
    val realCons = mkConstructor(realID)()(Some(tpeID))(_ => Seq())
    val real = T(realID)()

    val strID = FreshIdentifier("String")
    val strCons = mkConstructor(strID)()(Some(tpeID))(_ => Seq())
    val str = T(strID)()

    val tpeSort = mkSort(tpeID)()(Seq(
      botID, topID, clsID, adtID, arrID,
      setID, bagID, mapID, tplID, funID,
      boolID, intID, bvID, charID, unitID, realID, strID
    ))


    /* ====================================
     *             REF-TYPES ADT
     * ==================================== */

    val objID = FreshIdentifier("Object")
    val objPtr = FreshIdentifier("ptr")
    val objCons = mkConstructor(objID)()(None)(_ => Seq(ValDef(objPtr, IntegerType)))
    val obj = T(objID)()


    /* ====================================
     *         SUBTYPING FUNCTION
     * ==================================== */

    class TypeScope protected(val tparams: Map[s.TypeParameter, t.Expr]) extends ast.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(tp: s.Type): t.Type = tp match {
        case s.NothingType | s.AnyType | (_: s.ClassType) => obj
        case tp: s.TypeParameter if tparams contains tp => obj
        case (_: s.TypeBounds) | (_: s.UnionType) | (_: s.IntersectionType) =>
          throw MissformedStainlessCode(tp, "Unexpected type " + tp)
        case _ => super.transform(tp)
      }
    }

    object TypeScope {
      def empty = new TypeScope(Map.empty)

      def apply(cd: s.ClassDef, tpe: Expr): TypeScope = {
        val clsParams = cd.tparams.indices.map(i => seqAt(tpe.asInstOf(cls).getField(clsTps), i))
        val newTParams = (cd.tparams.map(_.tp) zip clsParams).toMap
        new TypeScope(newTParams)
      }

      def apply(d: s.ADTDefinition, tpe: Expr): TypeScope = {
        val adtParams = d.tparams.indices.map(i => seqAt(tpe.asInstOf(adt).getField(adtTps), i))
        val newTParams = (d.tparams.map(_.tp) zip adtParams).toMap
        new TypeScope(newTParams)
      }
    }

    def encodeType(tpe: s.Type)(implicit scope: TypeScope): t.Expr = tpe match {
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
      case tp: s.TypeParameter if scope.tparams contains tp => scope.tparams(tp)
      case tp: s.TypeParameter => top()
      case s.BooleanType => bool()
      case s.IntegerType => int()
      case s.BVType(size) => bv(IntegerLiteral(size))
      case s.CharType => char()
      case s.UnitType => unit()
      case s.RealType => real()
      case s.StringType => str()
      case _ => scala.sys.error("Unexpected type " + tpe)
    }

    val subtypeID = FreshIdentifier("isSubtypeOf")
    val subtypeOf = (e1: Expr, e2: Expr) => FunctionInvocation(subtypeID, Seq(), Seq(e1, e2))

    val subtypeFunction = mkFunDef(subtypeID, Unchecked)()(_ => (
      Seq("tp1" :: tpe, "tp2" :: tpe), BooleanType, {
        case Seq(tp1, tp2) => Seq(
          tp2.isInstOf(top) -> E(true),
          tp1.isInstOf(bot) -> E(true),
          tp1.isInstOf(cls) -> (
            tp2.isInstOf(cls) &&
            symbols.classes.values.foldRight(
              IfExpr(andJoin(symbols.classes.values.filter(_.flags contains s.IsSealed).toSeq.map {
                cd => !(tp2.asInstOf(cls).getField(clsPtr) === IntegerLiteral(cd.id.globalId))
              }), choose("res" :: BooleanType)(_ => E(true)), E(false)): Expr
            ) {
              case (cd, elze) => IfExpr(
                tp1.asInstOf(cls).getField(clsPtr) === IntegerLiteral(cd.id.globalId),
                (
                  tp2.asInstOf(cls).getField(clsPtr) === IntegerLiteral(cd.id.globalId) && {
                    def rec(tparams: Seq[s.TypeParameter], seq1: Expr, seq2: Expr): Expr = tparams match {
                      case tp +: xs =>
                        val (t1, t2) = (seq1.asInstOf(cons).getField(head), seq2.asInstOf(cons).getField(head))
                        val cond = if (tp.isCovariant) subtypeOf(t1, t2)
                          else if (tp.isContravariant) subtypeOf(t2, t1)
                          else t1 === t2
                        seq1.isInstOf(cons) &&
                        seq2.isInstOf(cons) &&
                        cond &&
                        rec(xs, seq1.asInstOf(cons).getField(tail), seq2.asInstOf(cons).getField(tail))
                      case Seq() => E(true)
                    }

                    rec(cd.typeArgs, tp1.asInstOf(cls).getField(clsTps), tp2.asInstOf(cls).getField(clsTps))
                  }
                ) || (
                  orJoin(cd.parents.map(ct => subtypeOf(encodeType(ct)(TypeScope(cd, tp1)), tp2)))
                ),
                elze
              )
            }
          ),
          tp1.isInstOf(adt) -> (
            tp2.isInstOf(adt) &&
            symbols.adts.values.foldRight(E(false)) {
              case (d, elze) => IfExpr(
                tp1.asInstOf(adt).getField(adtPtr) === IntegerLiteral(d.id.globalId),
                orJoin(Seq(d, d.root(symbols)).distinct.map {
                  d => tp2.asInstOf(adt).getField(adtPtr) === IntegerLiteral(d.id.globalId)
                }) && tp1.asInstOf(adt).getField(adtTps) === tp2.asInstOf(adt).getField(adtTps),
                elze
              )
            }
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
        ).foldRight((tp1 === tp2): Expr) {
          case ((cond, thenn), elze) => IfExpr(cond, thenn, elze)
        }
      }))

    def isObject(tpe: s.Type)(implicit scope: TypeScope): Boolean = tpe match {
      case _: s.ClassType => true
      case s.NothingType | s.AnyType => true
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
      Seq("e" :: obj, "tp2" :: tpe), BooleanType, {
        case Seq(e, tp2) => let("tp1" :: tpe, typeOf(e))(tp1 => Seq(
          tp2.isInstOf(bot) -> E(false),
          tp2.isInstOf(top) -> E(true),
          tp2.isInstOf(cls) -> (
            tp1.isInstOf(cls) &&
            andJoin(symbols.classes.values.toSeq.filter(_.flags contains s.IsAbstract).map {
              cd => !(tp1.asInstOf(cls).getField(clsPtr) === IntegerLiteral(cd.id.globalId))
            }) &&
            subtypeOf(tp1, tp2)
          ),
          tp2.isInstOf(adt) -> (
            tp1.isInstOf(adt) &&
            andJoin(symbols.adts.values.filter(_.isSort).toSeq.map {
              d => !(tp1.asInstOf(adt).getField(adtPtr) === IntegerLiteral(d.id.globalId))
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

    val fieldFunctions: Seq[t.FunDef] = typeFunction +: classFields.values.toSeq

    def getField(e: t.Expr, id: Identifier): t.Expr = FunctionInvocation(classFields(id).id, Seq(), Seq(e))

    val unwrapCache: MutableMap[t.Type, t.FunDef] = MutableMap.empty
    def unwrapFunctions: Seq[t.FunDef] = unwrapCache.values.toSeq

    def unwrap(e: t.Expr, expected: t.Type): t.Expr = {
      val fd = unwrapCache.getOrElseUpdate(expected, {
        mkFunDef(FreshIdentifier(encodeName("unwrap" + expected)), Unchecked)()(_ => (
          Seq("x" :: obj), expected, { case Seq(x) => choose("res" :: expected)(_ => E(true)) }
        ))
      })
      FunctionInvocation(fd.id, Seq(), Seq(e))
    }

    def wrap(e: t.Expr, tpe: t.Type): t.Expr = {
      choose(ValDef(FreshIdentifier("res"), obj, Set(Unchecked)))(res => unwrap(res, tpe) === e)
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
            Lambda(newArgs, newBody)
          case _ =>
            val newArgs = from2.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
            val appArgs = ((from1 zip from2) zip newArgs).map { case ((tp1, tp2), vd) =>
              rec(vd.toVariable, tp2, tp1)
            }
            val newBody = rec(Application(e, appArgs), to1, to2)
            Lambda(newArgs, newBody)
        }

        case (TupleType(tps1), TupleType(tps2)) => e match {
          case Tuple(es) => Tuple(((tps1 zip tps2) zip es).map {
            case ((tp1, tp2), e) => rec(e, tp1, tp2)
          })
          case _ => Tuple((tps1 zip tps2).zipWithIndex.map {
            case ((tp1, tp2), i) => rec(TupleSelect(e, i + 1), tp1, tp2)
          })
        }

        case (ADTType(id1, tps1), ADTType(id2, tps2)) =>
          val root = symbols.getADT(id1).root(symbols)
          val (tpe1, tpe2) = (ADTType(root.id, tps1), ADTType(root.id, tps2))

          val id = unificationCache.get((tpe1, tpe2)) match {
            case Some(fd) => fd.id
            case None => unifications.get((tpe1, tpe2)) match {
              case Some(id) => id
              case None =>
                val id = FreshIdentifier(encodeName("unify_" + tpe1 + "_" + tpe2))
                unifications += (tpe1, tpe2) -> id
                unificationCache += (tpe1, tpe2) -> mkFunDef(id, Unchecked)()(_ => (
                  Seq("e" :: tpe1), tpe2, { case Seq(e) =>
                    val conss = root match {
                      case cons: s.ADTConstructor => Seq(cons)
                      case sort: s.ADTSort => sort.constructors(symbols)
                    }

                    val scope = TypeScope.empty
                    val condRecons :+ ((_, last)) = conss.map { cons =>
                      val cond = IsInstanceOf(e, ADTType(cons.id, tps1))
                      val cast = AsInstanceOf(e, ADTType(cons.id, tps1))

                      val typeArgs = cons.typeArgs.map(scope.transform)

                      val fields = cons.fields.map { vd =>
                        val ttpe = scope.transform(vd.tpe)
                        def instantiate(tps: Seq[Type]): Type = {
                          val tpMap = (typeArgs zip tps).toMap
                          typeOps.postMap {
                            case tp: TypeParameter => tpMap.get(tp)
                            case _ => None
                          } (ttpe)
                        }
                        rec(ADTSelector(cast, vd.id), instantiate(tps1), instantiate(tps2))
                      }

                      (cond, ADT(ADTType(cons.id, tps2), fields))
                    }

                    condRecons.foldRight(last: Expr) { case ((cond, e), elze) => IfExpr(cond, e, elze) }
                  }
                ))
                id
            }
          }

          FunctionInvocation(id, Seq(), Seq(e))

        case (ArrayType(b1), ArrayType(b2)) => choose(ValDef(FreshIdentifier("res"), hi, Set(Unchecked))) {
          res => forall("i" :: Int32Type)(i => rec(ArraySelect(e, i), b1, b2) === ArraySelect(res, i))
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

    val option = symbols.lookup[s.ADTDefinition]("stainless.lang.Option").id
    val some = symbols.lookup[s.ADTDefinition]("stainless.lang.Some").id
    val none = symbols.lookup[s.ADTDefinition]("stainless.lang.None").id

    val unapplyAdtCache: MutableMap[Identifier, t.FunDef] = MutableMap.empty
    def getAdtUnapply(id: Identifier): Identifier = unapplyAdtCache.get(id) match {
      case Some(fd) => fd.id
      case None =>
        val cons = symbols.getADT(id).asInstanceOf[s.ADTConstructor]
        val arg = t.ValDef(FreshIdentifier("x"), obj)
        implicit val scope = TypeScope(cons, typeOf(arg.toVariable))
        val tt = t.tupleTypeWrap(
          cons.fields.map(vd => if (isSimple(vd.tpe)) scope.transform(vd.tpe) else obj) ++
          cons.tparams.map(_ => tpe)
        )

        val fd = mkFunDef(FreshIdentifier("unapply_" + id.name), Unchecked)()(_ => (
          Seq(arg), T(option)(tt), { case Seq(x) =>
            let("tpe" :: tpe, typeOf(x)) { tpe =>
              if_ (
                tpe.isInstOf(adt) &&
                tpe.asInstOf(adt).getField(adtPtr) === IntegerLiteral(id.globalId)
              ) {
                val unwrappedType = scope.transform(cons.typed(symbols).toType)
                let("uwrap" :: unwrappedType, unwrap(x, unwrappedType)) { uwrap =>
                  T(some)(tt)(tupleWrap(
                    cons.fields.map(vd => ADTSelector(uwrap, vd.id)) ++
                    cons.tparams.indices.map(i => seqAt(tpe.asInstOf(adt).getField(adtTps), i))
                  ))
                }
              } else_ {
                T(none)(tt)()
              }
            }
          }))
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
                tpe.isInstOf(cls) &&
                tpe.asInstOf(cls).getField(clsPtr) === IntegerLiteral(id.globalId)
              ) {
                T(some)(tt)(tupleWrap(
                  cd.fields.map(vd => getField(x, vd.id)) ++
                  cd.tparams.indices.map(i => seqAt(tpe.asInstOf(cls).getField(clsTps), i))
                ))
              } else_ {
                T(none)(tt)()
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
                tpe.isInstOf(tpl) &&
                (1 to size).foldLeft((E(true), x: Expr)) { case ((e, x), _) =>
                  (e && x.isInstOf(cons), x.asInstOf(cons).getField(tail))
                }._1
              ) {
                T(some)(tt)(unwrap(x, tt))
              } else_ {
                T(none)(tt)()
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

      protected implicit val scope = this

      def rewrite(id: Identifier): Boolean = functions(id).rewrite

      private def isSimpleFunction(fun: s.FunAbstraction): Boolean = {
        import symbols._

        var simple: Boolean = true
        object traverser extends s.TreeTraverser {
          protected def traversePattern(in: s.Expr, pat: s.Pattern): Unit = pat match {
            case s.WildcardPattern(_) =>
            case s.InstanceOfPattern(_, tpe) if !isSimple(leastUpperBound(in.getType, tpe)) => simple = false
            case s.ClassPattern(_, _, _) => simple = false
            case s.ADTPattern(ob, adt, subs) =>
              if (!isSimple(leastUpperBound(in.getType, adt))) simple = false
              else {
                val tcons = adt.getADT.toConstructor
                (tcons.fields zip subs).foreach(p => traversePattern(adtSelector(asInstOf(in, adt), p._1.id), p._2))
              }

            case s.TuplePattern(ob, subs) =>
              subs.zipWithIndex.foreach(p => traversePattern(tupleSelect(in, p._2 + 1, subs.size), p._1))

            case up @ s.UnapplyPattern(ob, id, tps, subs) =>
              (s.unwrapTuple(up.get(in), subs.size) zip subs) foreach (traversePattern _).tupled

            case s.LiteralPattern(_, lit) if !isSimple(leastUpperBound(in.getType, lit.getType)) => simple = false
            case _ =>
          }

          override def traverse(e: s.Expr): Unit = e match {
            case s.ClassConstructor(_, _) => simple = false
            case s.ClassSelector(_, _) => simple = false
            case s.MatchExpr(scrut, cases) => cases.foreach { case s.MatchCase(pat, _, _) => traversePattern(scrut, pat) }
            case s.IsInstanceOf(e, tpe) if !isSimple(leastUpperBound(e.getType, tpe)) => simple = false
            case s.AsInstanceOf(e, tpe) if !isSimple(leastUpperBound(e.getType, tpe)) => simple = false
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
          choose(ValDef(FreshIdentifier("ptr", true), IntegerType, Set(Unchecked))) { res =>
            typeOf(res) === encodeType(ct) &&
            andJoin((ct.tcd(symbols).fields zip args).map(p => getField(res, p._1.id) === transform(p._2)))
          }

        case s.ClassSelector(expr, id) =>
          getField(transform(expr), id)

        case s.IsInstanceOf(expr, tpe) if isObject(symbols.leastUpperBound(expr.getType(symbols), tpe)) =>
          instanceOf(transform(expr), encodeType(tpe))

        case s.AsInstanceOf(expr, tpe) if isObject(symbols.leastUpperBound(expr.getType(symbols), tpe)) =>
          val exprType = expr.getType(symbols)
          val te = transform(expr)
          val check = subtypeOf(if (isObject(exprType)) typeOf(te) else encodeType(exprType), encodeType(tpe))
          val result = if (isObject(exprType) && !isObject(tpe)) unwrap(te, transform(tpe))
            else if (!isObject(exprType) && isObject(tpe)) wrap(te, transform(tpe))
            else te

          t.Assert(check, Some("Cast error"), result)

        case (_: s.ADTSelector | _: s.MapApply) if isObject(e.getType(symbols)) =>
          let("res" :: tpe, super.transform(e)) { res =>
            t.Assume(instanceOf(res, encodeType(e.getType(symbols))), res)
          }

        case fi @ s.FunctionInvocation(id, tps, args) if scope rewrite id =>
          val fdScope = this in id
          val fd = symbols.getFunction(id)

          val newArgs = (fd.params zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transform(arg.getType(symbols)), fdScope.transform(vd.tpe))
          } ++ tps.map(encodeType)

          unifyTypes(
            t.FunctionInvocation(id, Seq(), newArgs),
            fdScope.transform(fd.returnType),
            transform(fi.getType(symbols))
          )

        case app @ s.ApplyLetRec(v, tparams, tps, args) if scope rewrite v.id =>
          val appScope = this in v.id
          val fun = functions(v.id).fun

          val newArgs = (fun.params zip args).map { case (vd, arg) =>
            unifyTypes(transform(arg), transform(arg.getType(symbols)), appScope.transform(vd.tpe))
          } ++ tps.map(encodeType)

          val vd @ t.ValDef(id, FunctionType(from, to), flags) = appScope.transform(v.toVal)
          val nvd = vd.copy(tpe = FunctionType(from ++ tparams.map(_ => tpe), to))

          unifyTypes(
            t.ApplyLetRec(nvd.toVariable, Seq(), Seq(), newArgs),
            appScope.transform(fun.returnType),
            transform(app.getType(symbols))
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
          t.MatchExpr(transform(scrut), for (cse <- cases) yield {
            val (newPattern, newGuard) = transformPattern(scrut, cse.pattern)
            val guard = t.andJoin(cse.optGuard.map(transform).toSeq ++ newGuard) match {
              case t.BooleanLiteral(true) => None
              case cond => Some(cond)
            }
            t.MatchCase(newPattern, guard, transform(cse.rhs))
          }).copiedFrom(e)

        case s.LetRec(fds, body) =>
          val funs = fds.map(fd => s.Inner(fd))
          val newScope = scope withFunctions funs
          val newFuns = funs.map(fun => transformFunction(fun)(newScope))
          val newBody = newScope.transform(body)
          t.LetRec(newFuns.map(_.toLocal), newBody).copiedFrom(e)

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
            if (isObject(leastUpperBound(in.getType, tpe))) {
              val v = transform(ob.map(_.toVariable).getOrElse(in))
              (t.WildcardPattern(ob map transform), instanceOf(v, encodeType(tpe)))
            } else {
              (t.InstanceOfPattern(ob map transform, transform(tpe)), t.BooleanLiteral(true))
            }

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

          case s.ADTPattern(ob, adt, subs) =>
            val v = ob.map(_.toVariable).getOrElse(in)
            val tcons = adt.getADT.toConstructor
            val rs = (tcons.fields zip subs).map(p => rec(adtSelector(asInstOf(v, adt), p._1.id), p._2))
            if (isObject(leastUpperBound(in.getType, adt))) {
              val (rsubs, rconds) = (rs ++ adt.tps.map(typePattern(_, None))).unzip
              (t.UnapplyPattern(ob map transform, getAdtUnapply(adt.id), Seq.empty, rsubs), andJoin(rconds))
            } else {
              val radt = transform(adt).asInstanceOf[t.ADTType]
              (t.ADTPattern(ob map transform, radt, rs.map(_._1)), t.andJoin(rs.map(_._2)))
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
            if (isObject(leastUpperBound(in.getType, lit.getType))) {
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
      import s.TypeParameterWithBounds
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
        val tparamParams = fd.tparams.map(tpd => t.ValDef(tpd.id.freshen, tpe))

        val tparamConds = fd.tparams.foldLeft(Seq[Expr]()) { case (conds, tpd) =>
          val v = scope.tparams(tpd.tp)
          val s.TypeBounds(lowerBound, upperBound) = tpd.tp.bounds
          conds ++ Seq(
            if (lowerBound != s.NothingType) subtypeOf(encodeType(lowerBound), v) else E(true),
            if (upperBound != s.AnyType) subtypeOf(v, encodeType(upperBound)) else E(true)
          )
        }

        val newParams = fd.params.map(scope.transform(_))

        val paramConds = (newParams zip fd.params.map(_.tpe)).map { case (vd, tpe) =>
          if (!isObject(tpe)) t.BooleanLiteral(true)
          else instanceOf(vd.toVariable, encodeType(tpe))
        }

        val returnType = scope.transform(fd.returnType)

        val (pre, body, post) = s.exprOps.breakDownSpecs(fd.fullBody)

        val newPre = t.andJoin(
          pre.map(scope.transform(_)).toSeq ++
          tparamConds ++
          paramConds
        ) match {
          case t.BooleanLiteral(true) => None
          case cond => Some(cond)
        }

        val newPost = {
          val Lambda(Seq(res), body) = post.map(scope.transform(_)).getOrElse(\("res" :: returnType)(_ => E(true)))
          val returnCond = if (isObject(fd.returnType)) {
            instanceOf(res.toVariable, encodeType(fd.returnType))
          } else {
            E(true)
          }

          and(body, returnCond) match {
            case t.BooleanLiteral(true) => None
            case cond => Some(Lambda(Seq(res), cond))
          }
        }

        val newBody = body.map(scope.transform)

        fd.to(t)(
          fd.id,
          Seq.empty,
          newParams ++ tparamParams,
          returnType,
          t.exprOps.reconstructSpecs(newPre, newBody, newPost, returnType),
          fd.flags map scope.transform
        )
      }
    }

    val symbolFuns = symbols.functions.values.map(s.Outer(_)).toSeq
    val baseScope = Scope.empty withFunctions symbolFuns

    val functions: Seq[t.FunDef] = symbolFuns.map(fd => transformFunction(fd)(baseScope).toFun)

    val adts: Seq[t.ADTDefinition] = symbols.adts.values.map(d => baseScope.transform(d)).toSeq

    val newSymbols = NoSymbols
      .withFunctions(
        Seq(subtypeFunction, instanceFunction) ++ 
        unapplyFunctions ++
        fieldFunctions ++
        unwrapFunctions ++
        unificationFunctions ++
        functions)
      .withADTs(Seq(
        seqSort, consCons, nilCons, tpeSort,
        botCons, topCons, clsCons, adtCons, arrCons,
        setCons, bagCons, mapCons, tplCons, funCons,
        boolCons, intCons, bvCons, charCons, unitCons, realCons, strCons,
        objCons
      ) ++ adts)

    def inlineChecks(e: Expr): Expr = {
      import newSymbols._
      import exprOps._

      exprOps.postMap {
        case fi @ FunctionInvocation(`subtypeID`, Seq(), Seq(
          ADT(`tpl`, Seq(ADTSelector(_, `tail`))),
          ADT(`tpl`, Seq(ADTSelector(_, `tail`)))
        )) => None

        case fi @ FunctionInvocation(`subtypeID`, Seq(), Seq(
          ADT(`fun`, Seq(ADTSelector(_, `tail`), _)),
          ADT(`fun`, Seq(ADTSelector(_, `tail`), _))
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
      .withADTs(newSymbols.adts.values.toSeq)

    for (fd <- finalSymbols.functions.values) {
      if (!finalSymbols.isSubtypeOf(fd.fullBody.getType(finalSymbols), fd.returnType)) {
        println(fd)
        println(finalSymbols.explainTyping(fd.fullBody)(PrinterOptions()))
      }
    }

    finalSymbols
  }
}
