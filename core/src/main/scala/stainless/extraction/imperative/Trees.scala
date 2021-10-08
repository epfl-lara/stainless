/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position
import inox.transformers.Transformer
import stainless.transformers.TreeTransformer
import stainless.transformers.TreeTraverser

trait Trees extends oo.Trees with Definitions { self =>

  /* XLang imperative trees to desugar */

  /** Return an [[ast.Expressions.Expr]].
    *
    * @param expr The expression to return
    */
  sealed case class Return(expr: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type =
      if (expr.isTyped) NothingType() else Untyped
  }

  /** Swap indices from two (not necessarily distinct) arrays */
  sealed case class Swap(array1: Expr, index1: Expr, array2: Expr, index2: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type =
      (array1.getType, array2.getType) match {
        case (ArrayType(base1), ArrayType(base2)) if base1 == base2 =>
          checkParamTypes(Seq(index1, index2), Seq(Int32Type(), Int32Type()), UnitType())
        case _ =>
          Untyped
      }
  }

  /** $encodingof `{ expr1; expr2; ...; exprn; last }` */
  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type = if (exprs.forall(_.isTyped)) last.getType else Untyped
  }

  /** $encoding of `var vd = value; body` */
  case class LetVar(vd: ValDef, value: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type =
      checkParamType(value, vd.tpe, body.getType)
  }

  /** $encodingof `vd = value` */
  case class Assignment(v: Variable, value: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type =
      checkParamType(value, v.tpe, UnitType())
  }

  /** $encodingof `obj.selector = value` */
  case class FieldAssignment(obj: Expr, selector: Identifier, value: Expr) extends Expr with CachingTyped {
    def getField(using Symbols): Option[ValDef] = getClassType(obj) match {
      case ct: ClassType => ct.getField(selector)
      case _ => getADTType(obj) match {
        case adt: ADTType => adt.getField(selector)
        case _ => None
      }
    }

    protected def computeType(using s: Symbols): Type = {
      getField
        .filter(vd => s.isSubtypeOf(value.getType, vd.tpe))
        .map(_ => UnitType())
        .getOrElse(Untyped)
    }
  }

  /** $encodingof `(while(cond) { ... }).invariant(pred).noReturnInvariant(pred2)`*/
  case class While(cond: Expr, body: Expr, pred: Option[Expr], pred2: Option[Expr], flags: Seq[Flag]) extends Expr with CachingTyped {
    protected def computeType(using s: Symbols): Type =
      if (
        s.isSubtypeOf(cond.getType, BooleanType()) &&
        body.isTyped &&
        pred.forall(p => s.isSubtypeOf(p.getType, BooleanType())) &&
        pred2.forall(p => s.isSubtypeOf(p.getType, BooleanType()))
      ) UnitType() else Untyped
  }

  /** $encodingof `array(index) = value` */
  case class ArrayUpdate(array: Expr, index: Expr, value: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type = array.getType match {
      case ArrayType(base) => checkParamTypes(Seq(index, value), Seq(Int32Type(), base), UnitType())
      case _ => Untyped
    }
  }


  /* Mutable Map Operations */

  sealed case class MutableMapType(from: Type, to: Type) extends Type

  /** $encodingof `MutableMap.withDefaultValue[From,To](default)` */
  sealed case class MutableMapWithDefault(from: Type, to: Type, default: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type = {
      checkParamType(default, FunctionType(Seq(), to), unveilUntyped(MutableMapType(from, to)))
    }
  }

  /** $encodingof `map.apply(key)` (or `map(key)`) */
  sealed case class MutableMapApply(map: Expr, key: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type = map.getType match {
      case MutableMapType(from, to) => checkParamType(key, from, to)
      case _ => Untyped
    }
  }

  /** $encodingof `map.updated(key, value)` (or `map + (key -> value)`) */
  sealed case class MutableMapUpdated(map: Expr, key: Expr, value: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type = map.getType match {
      case mmt @ MutableMapType(from, to) => checkParamTypes(Seq(key, value), Seq(from, to), MutableMapType(from, to))
      case _ => Untyped
    }
  }

  /** $encodingof `map.duplicate()` */
  sealed case class MutableMapDuplicate(map: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type = map.getType
  }

  /** $encodingof `map.update(key, value)` (or `map(key) = value`) */
  sealed case class MutableMapUpdate(map: Expr, key: Expr, value: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type = map.getType match {
      case mmt @ MutableMapType(from, to) => checkParamTypes(Seq(key, value), Seq(from, to), UnitType())
      case _ => Untyped
    }
  }

  /** $encodingof `old(e)` */
  case class Old(e: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type = e.getType
  }

  /** $encodingof `snapshot(e)` */
  case class Snapshot(e: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type = e.getType
  }

  /** copy primitive, like `Snapshot` but usable outside of the ghost context. Mostly to work-around anti-aliasing. */
  case class FreshCopy(e: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type = e.getType
  }

  /** $encodingof `a & b` for Boolean; desuggared to { val l = lhs; val r = rhs; l && r } when removing imperative style. */
  case class BoolBitwiseAnd(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type =
      checkAllTypes(Seq(lhs, rhs), BooleanType(), BooleanType())
  }

  /** $encodingof `a | b` for Boolean; desuggared to { val l = lhs; val r = rhs; l || r } when removing imperative style. */
  case class BoolBitwiseOr(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type =
      checkAllTypes(Seq(lhs, rhs), BooleanType(), BooleanType())
  }

  /** $encodingof `a ^ b` for Boolean; desuggared to { val l = lhs; val r = rhs; l != r } when removing imperative style. */
  case class BoolBitwiseXor(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type =
      checkAllTypes(Seq(lhs, rhs), BooleanType(), BooleanType())
  }

  /** An extractor for the AnyHeapRef type in the stainless.lang package */
  object AnyHeapRefType {
    // TODO(gsps): Cache this ClassDef
    def classDefOpt(using s: Symbols): Option[ClassDef] =
      s.lookup.get[ClassDef]("stainless.lang.AnyHeapRef")

    def apply()(using Symbols): Type =
      classDefOpt.get.typed.toType

    def unapply(tpe: Type)(using Symbols): Boolean = tpe match {
      case ct: ClassType => classDefOpt.map(_.id == ct.id).getOrElse(false)
      case _ => false
    }
  }

  /** Represents a `reads(objs)` contract. `objs` should be a set of references, and the body is what follows the contract. */
  case class Reads(objs: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(using s: Symbols): Type = objs.getType match {
      case SetType(objTpe) if s.isSubtypeOf(objTpe, AnyHeapRefType()) => body.getType
      case _ => Untyped
    }
  }

  /** Represents a `modifies(objs)` contract. `objs` should be a set of references, and the body is what follows the contract. */
  case class Modifies(objs: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(using s: Symbols): Type = objs.getType match {
      case SetType(objTpe) if s.isSubtypeOf(objTpe, AnyHeapRefType()) => body.getType
      case _ => Untyped
    }
  }

  object VarDef {
    def apply(id: Identifier, tpe: Type, flags: Seq[Flag]): ValDef = ValDef(id, tpe, (flags :+ IsVar).distinct)
    def unapply(d: Definition): Option[(Identifier, Type, Seq[Flag])] = d match {
      case vd: ValDef if vd.flags contains IsVar => Some((vd.id, vd.tpe, vd.flags))
      case _ => None
    }
  }

  override implicit def convertToVal = new VariableConverter[ValDef] {
    def convert(vs: VariableSymbol): ValDef = vs match {
      case VarDef(id, tpe, flags) => ValDef(id, tpe, flags filter (_ != IsVar)).copiedFrom(vs)
      case vd: ValDef => vd
      case _ => ValDef(vs.id, vs.tpe, vs.flags).copiedFrom(vs)
    }
  }

  extension (vs: VariableSymbol) {
    def toVar: ValDef = vs match {
      case vd: ValDef if vd.flags contains IsVar => vd
      case vd: ValDef => VarDef(vd.id, vd.tpe, vd.flags :+ IsVar).copiedFrom(vs)
      case _ => ValDef(vs.id, vs.tpe, (vs.flags :+ IsVar).distinct).copiedFrom(vs)
    }
  }

  case object IsVar extends Flag("var", Seq.empty)
  case object IsPure extends Flag("pure", Seq.empty)
  case object IsMutable extends Flag("mutable", Seq.empty)

  override val exprOps: ExprOps { val trees: self.type } = {
    class ExprOpsImpl(override val trees: self.type) extends ExprOps(trees)
    new ExprOpsImpl(self)
  }


  /* ========================================
   *               EXTRACTORS
   * ======================================== */

  override def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("pure", Seq()) => IsPure
    case ("mutable", Seq()) => IsMutable
    case _ => super.extractFlag(name, args)
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
      class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
      new DeconstructorImpl(self, tree)

    case _ => super.getDeconstructor(that)
  }

  /* ========================================
   *               HEAP ENCODING
   * ======================================== */

  private[this] lazy val heapRefId: Identifier = ast.SymbolIdentifier("stainless.lang.HeapRef")
  private[this] lazy val heapRefCons: Identifier = ast.SymbolIdentifier("stainless.lang.HeapRef")
  lazy val heapRefSort: ADTSort = dsl.mkSort(heapRefId)() { _ =>
    Seq((heapRefCons, Seq(ValDef(FreshIdentifier("id"), IntegerType()))))
  }

  private[this] lazy val dummyHeapId: Identifier = ast.SymbolIdentifier("stainless.lang.dummyHeap")
  lazy val dummyHeap: FunDef = dsl.mkFunDef(dummyHeapId, Synthetic, Extern)() { _ =>
    (Seq(), HeapMapType, { _ => NoTree(HeapMapType) })
  }

  lazy val HeapRefType: Type = ADTType(heapRefId, Seq.empty)
  lazy val HeapRefSetType: Type = SetType(HeapRefType)
  lazy val HeapMapType: MapType = MapType(HeapRefType, AnyType())
}

trait Printer extends oo.Printer {
  protected val trees: Trees
  import trees._

  override protected def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
    case Block(exprs, last) =>
      p"${nary(exprs :+ last, "\n")}"

    case Return(e) =>
      p"return $e"

    case Swap(array1, index1, array2, index2) =>
      p"swap($array1, $index1, $array2, $index2)"

    case LetVar(vd, value, expr) =>
      p"""|var $vd = $value
          |$expr"""

    case Assignment(v, value) =>
      p"$v = $value"

    case FieldAssignment(obj, selector, value) =>
      p"$obj.$selector = $value"

    case While(cond, body, inv, weakInv, flags) =>
      inv.foreach(p => p"""|@invariant($p)
                           |""")
      weakInv.foreach(p => p"""|@noReturnInvariant($p)
                           |""")
      for (f <- flags) p"""|@${f.asString(using ctx.opts)}
                           |"""
      p"""|while ($cond) {
          |  $body
          |}"""

    case ArrayUpdate(array, index, value) =>
      p"$array($index) = $value"

    case MutableMapType(from,to) =>
      p"MutableMap[$from,$to]"

    case MutableMapWithDefault(from, to, default) =>
      p"MutableMap.withDefaultValue[$from,$to]($default)"

    case MutableMapApply(map, index) =>
      p"$map($index)"

    case MutableMapUpdate(map, key, value) =>
      p"$map($key) = $value"

    case MutableMapUpdated(map, key, value) =>
      p"$map.updated($key, $value)"

    case MutableMapDuplicate(map) =>
      p"$map.duplicate()"

    case Old(e) =>
      p"old($e)"

    case Snapshot(e) =>
      p"snapshot($e)"

    case FreshCopy(e) =>
      p"freshCopy($e)"

    case BoolBitwiseAnd(lhs, rhs) => optP {
      p"$lhs & $rhs"
    }

    case BoolBitwiseOr(lhs, rhs) => optP {
      p"$lhs | $rhs"
    }

    case BoolBitwiseXor(lhs, rhs) => optP {
      p"$lhs ^ $rhs"
    }

    case Reads(objs, body) =>
      p"""|reads($objs);
          |$body"""

    case Modifies(objs, body) =>
      p"""|modifies($objs);
          |$body"""

    case _ => super.ppBody(tree)
  }

  override protected def isSimpleExpr(e: Expr): Boolean = e match {
    case (_: Block) | (_: LetVar) | (_: Reads) | (_: Modifies) => false
    case _ => super.isSimpleExpr(e)
  }

  override protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case LetVar(_, _, bd) => Seq(bd)
    case Return(e) => Seq(e)
    case Reads(_, bd) => Seq(bd)
    case Modifies(_, bd) => Seq(bd)
    case _ => super.noBracesSub(e)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: Return)) => false
    case _ => super.requiresParentheses(ex, within)
  }

  override protected def requiresBraces(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_: Expr, Some(_: Block)) => false
    case (_: Block, Some(_: While)) => false
    case _ => super.requiresBraces(ex, within)
  }
}

trait TreeDeconstructor extends oo.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.BoolBitwiseAnd(lhs, rhs) =>
      (Seq(), Seq(), Seq(lhs, rhs), Seq(), Seq(), (_, _, es, _, _) => t.BoolBitwiseAnd(es(0), es(1)))

    case s.BoolBitwiseOr(lhs, rhs) =>
      (Seq(), Seq(), Seq(lhs, rhs), Seq(), Seq(), (_, _, es, _, _) => t.BoolBitwiseOr(es(0), es(1)))

    case s.BoolBitwiseXor(lhs, rhs) =>
      (Seq(), Seq(), Seq(lhs, rhs), Seq(), Seq(), (_, _, es, _, _) => t.BoolBitwiseXor(es(0), es(1)))

    case s.Block(exprs, last) =>
      (Seq(), Seq(), exprs :+ last, Seq(), Seq(), (_, _, es, _, _) => t.Block(es.init, es.last))

    case s.LetVar(vd, value, expr) =>
      (Seq(), Seq(vd.toVariable), Seq(value, expr), Seq(), Seq(), (_, vs, es, _, _) => t.LetVar(vs.head.toVal, es(0), es(1)))

    // @nv: we DON'T return `v` as a variable here as it should not be removed from the
    //      set of free variables in `e`!
    case s.Assignment(v, value) =>
      (Seq(), Seq(), Seq(v, value), Seq(), Seq(), (_, _, es, _, _) => t.Assignment(es(0).asInstanceOf[t.Variable], es(1)))

    case s.FieldAssignment(obj, selector, value) =>
      (Seq(selector), Seq(), Seq(obj, value), Seq(), Seq(), (ids, _, es, _, _) => t.FieldAssignment(es(0), ids.head, es(1)))

    case s.While(cond, body, pred, None, flags) =>
      (Seq(), Seq(), Seq(cond, body) ++ pred, Seq(), flags, (_, _, es, _, newFlags) =>
        t.While(es(0), es(1), es.drop(2).headOption, None, newFlags))

    case s.While(cond, body, None, pred, flags) =>
      (Seq(), Seq(), Seq(cond, body) ++ pred, Seq(), flags, (_, _, es, _, newFlags) =>
        t.While(es(0), es(1), None, es.drop(2).headOption, newFlags))

    case s.While(cond, body, Some(inv), Some(weakInv), flags) =>
      (Seq(), Seq(), Seq(cond, body, inv, weakInv), Seq(), flags, (_, _, es, _, newFlags) =>
        t.While(es(0), es(1), Some(es(2)), Some(es(3)), newFlags))

    case s.ArrayUpdate(array, index, value) =>
      (Seq(), Seq(), Seq(array, index, value), Seq(), Seq(), (_, _, es, _, _) => t.ArrayUpdate(es(0), es(1), es(2)))

    case s.Old(e) =>
      (Seq(), Seq(), Seq(e), Seq(), Seq(), (_, _, es, _, _) => t.Old(es.head))

    case s.Return(e) =>
      (Seq(), Seq(), Seq(e), Seq(), Seq(), (_, _, es, _, _) => t.Return(es(0)))

    case s.Swap(array1, index1, array2, index2) =>
      (Seq(), Seq(), Seq(array1, index1, array2, index2), Seq(), Seq(), (_, _, es, _, _) => t.Swap(es(0), es(1), es(2), es(3)))

    case s.MutableMapWithDefault(from, to, default) =>
      (Seq(), Seq(), Seq(default), Seq(from, to), Seq(), (_, _, es, tps, _) => t.MutableMapWithDefault(tps(0), tps(1), es(0)))

    case s.MutableMapApply(map, index) =>
      (Seq(), Seq(), Seq(map, index), Seq(), Seq(), (_, _, es, _, _) => t.MutableMapApply(es(0), es(1)))

    case s.MutableMapUpdate(map, key, value) =>
      (Seq(), Seq(), Seq(map, key, value), Seq(), Seq(), (_, _, es, _, _) => t.MutableMapUpdate(es(0), es(1), es(2)))

    case s.MutableMapUpdated(map, key, value) =>
      (Seq(), Seq(), Seq(map, key, value), Seq(), Seq(), (_, _, es, _, _) => t.MutableMapUpdated(es(0), es(1), es(2)))

    case s.MutableMapDuplicate(map) =>
      (Seq(), Seq(), Seq(map), Seq(), Seq(), (_, _, es, _, _) => t.MutableMapDuplicate(es(0)))

    case s.Snapshot(e) =>
      (Seq(), Seq(), Seq(e), Seq(), Seq(), (_, _, es, _, _) => t.Snapshot(es.head))

    case s.FreshCopy(e) =>
      (Seq(), Seq(), Seq(e), Seq(), Seq(), (_, _, es, _, _) => t.FreshCopy(es.head))

    case s.Reads(objs, bd) =>
      (Seq(), Seq(), Seq(objs, bd), Seq(), Seq(), (_, _, es, _, _) => t.Reads(es(0), es(1)))

    case s.Modifies(objs, bd) =>
      (Seq(), Seq(), Seq(objs, bd), Seq(), Seq(), (_, _, es, _, _) => t.Modifies(es(0), es(1)))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(tpe: s.Type): Deconstructed[t.Type] = tpe match {
    case s.MutableMapType(from, to) => (Seq(), Seq(), Seq(), Seq(from, to), Seq(), (_, _, _, tps, _) => t.MutableMapType(tps(0), tps(1)))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.IsVar => (Seq(), Seq(), Seq(), (_, _, _) => t.IsVar)
    case s.IsPure => (Seq(), Seq(), Seq(), (_, _, _) => t.IsPure)
    case s.IsMutable => (Seq(), Seq(), Seq(), (_, _, _) => t.IsMutable)
    case _ => super.deconstruct(f)
  }
}

class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor

class ExprOps(override val trees: Trees) extends oo.ExprOps(trees) { self =>
  import trees._

  /** The two new kinds of contracts that the imperative phase introduces */
  object ReadsKind extends SpecKind("reads") { type Spec = ReadsContract }
  object ModifiesKind extends SpecKind("modifies") { type Spec = ModifiesContract }

  /** Reads contract that corresponds to [[Expressions.Reads]]. */
  case class ReadsContract(expr: Expr) extends Specification(ReadsKind) {
    def transform(tr: Transformer { val s: trees.type; val t: ast.Trees })(env: tr.Env): tr.t.exprOps.Specification = tr.t match {
      case ot: imperative.Trees =>
        // The goal is to work-around the following expression that causes scalac 2.13 to fail codegen
        // for the cast of tr.transform(expr, env) into ot.Expr (probably due to `ot` being bound by a pattern match):
        //
        //      ot.exprOps.ReadsContract(tr.transform(expr, env).asInstanceOf[ot.Expr])
        //          .setPos(this).asInstanceOf[tr.t.exprOps.Specification]
        //
        val otExpr: ot.Expr = tr.transform(expr, env) match {
          // doing case e: ot.Expr triggers a compile-time error, but not if we mix it with tr.t.Expr...
          case e: tr.t.Expr with ot.Expr => e
        }
        ot.exprOps.ReadsContract(otExpr).setPos(this).asInstanceOf[tr.t.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't transform imperative into non-imperative trees")
    }

    def transform(tr: TreeTransformer { val s: trees.type; val t: ast.Trees }): tr.t.exprOps.Specification = {
      tr.t match {
        case ot: imperative.Trees =>
          // Same story here
          val otExpr: ot.Expr = tr.transform(expr) match {
            case e: tr.t.Expr with ot.Expr => e
          }
          ot.exprOps.ReadsContract(otExpr).asInstanceOf[tr.t.exprOps.Specification]
        case _ =>
          throw new java.lang.IllegalArgumentException("Can't transform imperative into non-imperative trees")
      }
    }

    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit =
      tr.traverse(expr)

    def isTrivial: Boolean = expr match {
      case FiniteSet(Seq(), _) => true
      case _ => false
    }

    def letWrapped(specced: BodyWithSpecs): ReadsContract =
      ReadsContract(specced.wrapLets(expr)).setPos(this.getPos)
  }

  /** Modifies contract that corresponds to [[Expressions.Modifies]]. */
  case class ModifiesContract(expr: Expr) extends Specification(ModifiesKind) {
    def transform(tr: Transformer { val s: trees.type; val t: ast.Trees })(env: tr.Env): tr.t.exprOps.Specification = tr.t match {
      case ot: imperative.Trees =>
        // See ReadsContract#transform for the reasons of this strange pattern match.
        val otExpr: ot.Expr = tr.transform(expr, env) match {
          case e: tr.t.Expr with ot.Expr => e
        }
        ot.exprOps.ModifiesContract(otExpr).setPos(this).asInstanceOf[tr.t.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't transform imperative into non-imperative trees")
    }

    def transform(tr: TreeTransformer { val s: trees.type; val t: ast.Trees }): tr.t.exprOps.Specification = tr.t match {
      case ot: imperative.Trees =>
        // Ditto
        val otExpr: ot.Expr = tr.transform(expr) match {
          case e: tr.t.Expr with ot.Expr => e
        }
        ot.exprOps.ModifiesContract(otExpr).setPos(this).asInstanceOf[tr.t.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't transform imperative into non-imperative trees")
    }

    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit =
      tr.traverse(expr)

    def isTrivial: Boolean = expr match {
      case FiniteSet(Seq(), _) => true
      case _ => false
    }

    def letWrapped(specced: BodyWithSpecs): ModifiesContract =
      ModifiesContract(specced.wrapLets(expr)).setPos(this.getPos)
  }

  /** Overridden to extract the specification from an expression */
  override def peelSpec(expr: Expr): Option[(Specification, Expr)] = expr match {
    case Reads(objs, body) => Some((ReadsContract(objs).setPos(expr), body))
    case Modifies(objs, body) => Some((ModifiesContract(objs).setPos(expr), body))
    case LetVar(vd, e, body) => Some((LetInSpec(vd, e).setPos(expr), body))
    case _ => super.peelSpec(expr)
  }

  /** Overridden to add a specification to an expression */
  override def applySpec(spec: Specification, body: Expr): Expr = spec match {
    case ReadsContract(objs) => Reads(objs, body).setPos(spec)
    case ModifiesContract(objs) => Modifies(objs, body).setPos(spec)
    case _ => super.applySpec(spec, body)
  }

  /** Returns the reads and modifies contracts of a function */
  final def heapContractsOf(body: Expr): (Option[Expr], Option[Expr]) = {
    val withSpecs = BodyWithSpecs(body)
    (withSpecs.getSpec(ReadsKind).map(_.expr), withSpecs.getSpec(ModifiesKind).map(_.expr))
  }

  /*
   * The level of effects of a function.
   * None = pure, doesn't read nor write to the heap
   * Some(false), reads but doesn't write to the heap
   * Some(true), reads and writes to the heap
   */
  type EffectLevel = Option[Boolean]

  /** Returns the effect level of a function. None = pure, Some(false) = reads, Some(true) = modifies */
  def getEffectLevel(fd: FunDef): EffectLevel = {
    def isContractEmpty(contract: Option[Expr]): Boolean = contract match {
      case None => true // We assume that omitting a contract is the same as an empty contract
      case Some(FiniteSet(Seq(), _)) => true
      case _ => false
    }

    val (reads, modifies) = heapContractsOf(fd.fullBody)
    if (isContractEmpty(modifies))
      if (isContractEmpty(reads)) None
      else Some(false)
    else Some(true)
  }

  def flattenBlocks(expr: Expr): Expr = postMap {
    case Block(exprs, last) =>
      val newExprs = (exprs.filter(_ != UnitLiteral()) :+ last).flatMap {
        case Block(es, l) => es :+ l
        case e => Seq(e)
      }

      Some(newExprs match {
        case Seq() => UnitLiteral()
        case Seq(e) => e
        case es => Block(es.init, es.last).setPos(Position.between(es.head.getPos, es.last.getPos))
      })
    case _ => None
  } (expr)

  /** Traverses [[expr]] top-down and _as soon as_ a visited expression occurs
    * in the [[subst]] map, replaces it by the corresponding image. The function
    * is NOT called recursively on the image!
    *
    * We use this to replace `Old(v)` expressions at the same time as we're
    * rewritting the `v` variable to some other expression. The non-recursivity
    * enables us to exclusively update one or the other.
    */
  def replaceSingle(subst: Map[Expr, Expr], expr: Expr): Expr = {
    def rec(e: Expr): Expr = subst.get(e) match {
      case Some(img) => img
      case None =>
        val Operator(es, recons) = e
        val newEs = es.map(rec)
        if ((es zip newEs) exists (p => p._1 ne p._2)) {
          recons(newEs).copiedFrom(e)
        } else {
          e
        }
    }

    rec(expr)
  }


  /* =============================
   * Freshening of local variables
   * ============================= */

  protected class ImperativeFreshener(freshenChooses: Boolean)
    extends OOFreshener(freshenChooses) {

    override def transform(e: Expr, env: Env): Expr = e match {
      case LetVar(vd, v, b) =>
        val freshVd = vd.freshen
        LetVar(transform(freshVd, env), transform(v, env), transform(b, env.updated(vd.id, freshVd.id))).copiedFrom(e)

      case _ => super.transform(e, env)
    }
  }

  override def freshenLocals(expr: Expr, freshenChooses: Boolean = false): Expr = {
    new ImperativeFreshener(freshenChooses).transform(expr, Map.empty[Identifier, Identifier])
  }

}
