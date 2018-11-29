/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position

trait Trees extends innerfuns.Trees with Definitions { self =>

  /* XLang imperative trees to desugar */

  /** $encodingof `{ expr1; expr2; ...; exprn; last }` */
  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = if (exprs.forall(_.isTyped)) last.getType else Untyped
  }

  /** $encoding of `var vd = value; body` */
  case class LetVar(vd: ValDef, value: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      checkParamType(value, vd.tpe, body.getType)
  }

  /** $encodingof `vd = value` */
  case class Assignment(v: Variable, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      checkParamType(value, v.tpe, UnitType())
  }

  // Override point for alternative field assignment targets
  protected def getField(tpe: Type, selector: Identifier)(implicit s: Symbols): Option[ValDef] = tpe match {
    case adt: ADTType => adt.getField(selector)
    case _ => None
  }

  /** $encodingof `obj.selector = value` */
  case class FieldAssignment(obj: Expr, selector: Identifier, value: Expr) extends Expr with CachingTyped {
    def getField(implicit s: Symbols): Option[ValDef] = self.getField(obj.getType, selector)

    protected def computeType(implicit s: Symbols): Type = {
      getField
        .filter(vd => s.isSubtypeOf(value.getType, vd.tpe))
        .map(_ => UnitType())
        .getOrElse(Untyped)
    }
  }

  /** $encodingof `(while(cond) { ... }) invariant (pred)` */
  case class While(cond: Expr, body: Expr, pred: Option[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (
        s.isSubtypeOf(cond.getType, BooleanType()) &&
        body.isTyped &&
        pred.forall(p => s.isSubtypeOf(p.getType, BooleanType()))
      ) UnitType() else Untyped
  }

  /** $encodingof `array(index) = value` */
  case class ArrayUpdate(array: Expr, index: Expr, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = array.getType match {
      case ArrayType(base) => checkParamTypes(Seq(index, value), Seq(Int32Type(), base), UnitType())
      case _ => Untyped
    }
  }


  /* Mutable Map Operations */

  sealed case class MutableMapType(from: Type, to: Type) extends Type

  /** $encodingof `MutableMap.withDefaultValue[From,To](default)` */
  sealed case class MutableMapWithDefault(from: Type, to: Type, default: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = {
      checkParamType(default, FunctionType(Seq(), to), unveilUntyped(MutableMapType(from, to)))
    }
  }

  /** $encodingof `map.apply(key)` (or `map(key)`) */
  sealed case class MutableMapApply(map: Expr, key: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = map.getType match {
      case MutableMapType(from, to) => checkParamType(key, from, to)
      case _ => Untyped
    }
  }

  /** $encodingof `map.updated(key, value)` (or `map + (key -> value)`) */
  sealed case class MutableMapUpdated(map: Expr, key: Expr, value: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = map.getType match {
      case mmt @ MutableMapType(from, to) => checkParamTypes(Seq(key, value), Seq(from, to), MutableMapType(from, to))
      case _ => Untyped
    }
  }

  /** $encodingof `map.duplicate()` */
  sealed case class MutableMapDuplicate(map: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = map.getType
  }

  /** $encodingof `map.update(key, value)` (or `map(key) = value`) */
  sealed case class MutableMapUpdate(map: Expr, key: Expr, value: Expr) extends Expr with CachingTyped {
    override protected def computeType(implicit s: Symbols): Type = map.getType match {
      case mmt @ MutableMapType(from, to) => checkParamTypes(Seq(key, value), Seq(from, to), UnitType())
      case _ => Untyped
    }
  }

  /** $encodingof `old(e)` */
  case class Old(e: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = e.getType
  }

  /** $encodingof `a & b` for Boolean; desuggared to { val l = lhs; val r = rhs; l && r } when removing imperative style. */
  case class BoolBitwiseAnd(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      checkAllTypes(Seq(lhs, rhs), BooleanType(), BooleanType())
  }

  /** $encodingof `a | b` for Boolean; desuggared to { val l = lhs; val r = rhs; l || r } when removing imperative style. */
  case class BoolBitwiseOr(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      checkAllTypes(Seq(lhs, rhs), BooleanType(), BooleanType())
  }

  /** $encodingof `a ^ b` for Boolean; desuggared to { val l = lhs; val r = rhs; l != r } when removing imperative style. */
  case class BoolBitwiseXor(lhs: Expr, rhs: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      checkAllTypes(Seq(lhs, rhs), BooleanType(), BooleanType())
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

  implicit class VariableSymbolToVar(vs: VariableSymbol) {
    def toVar: ValDef = vs match {
      case vd: ValDef if vd.flags contains IsVar => vd
      case vd: ValDef => VarDef(vd.id, vd.tpe, vd.flags :+ IsVar).copiedFrom(vs)
      case _ => ValDef(vs.id, vs.tpe, (vs.flags :+ IsVar).distinct).copiedFrom(vs)
    }
  }

  case object IsVar extends Flag("var", Seq.empty)
  case object IsPure extends Flag("pure", Seq.empty)
  case object IsMutable extends Flag("mutable", Seq.empty)

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps


  /* ========================================
   *               EXTRACTORS
   * ======================================== */

  override def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("pure", Seq()) => IsPure
    case ("mutable", Seq()) => IsMutable
    case _ => super.extractFlag(name, args)
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees =>new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait Printer extends innerfuns.Printer {
  protected val trees: Trees
  import trees._

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Block(exprs, last) =>
      p"${nary(exprs :+ last, "\n")}"

    case LetVar(vd, value, expr) =>
      p"""|var $vd = $value
          |$expr"""

    case Assignment(v, value) =>
      p"$v = $value"

    case FieldAssignment(obj, selector, value) =>
      p"$obj.$selector = $value"

    case While(cond, body, inv) =>
      inv.foreach(p => p"""|@invariant($p)
                           |""")
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

    case BoolBitwiseAnd(lhs, rhs) => optP {
      p"$lhs & $rhs"
    }

    case BoolBitwiseOr(lhs, rhs) => optP {
      p"$lhs | $rhs"
    }

    case BoolBitwiseXor(lhs, rhs) => optP {
      p"$lhs ^ $rhs"
    }

    case _ => super.ppBody(tree)
  }

  override protected def isSimpleExpr(e: Expr): Boolean = e match {
    case (_: Block) | (_: LetVar) => false
    case _ => super.isSimpleExpr(e)
  }

  override protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case LetVar(_, _, bd) => Seq(bd)
    case _ => super.noBracesSub(e)
  }

  override protected def requiresBraces(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_: Expr, Some(_: Block)) => false
    case (_: Block, Some(_: While)) => false
    case _ => super.requiresBraces(ex, within)
  }
}

trait TreeDeconstructor extends innerfuns.TreeDeconstructor {
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

    case s.While(cond, body, pred) =>
      (Seq(), Seq(), Seq(cond, body) ++ pred, Seq(), Seq(), (_, _, es, _, _) => t.While(es(0), es(1), es.drop(2).headOption))

    case s.ArrayUpdate(array, index, value) =>
      (Seq(), Seq(), Seq(array, index, value), Seq(), Seq(), (_, _, es, _, _) => t.ArrayUpdate(es(0), es(1), es(2)))

    case s.Old(e) =>
      (Seq(), Seq(), Seq(e), Seq(), Seq(), (_, _, es, _, _) => t.Old(es.head))

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

trait ExprOps extends innerfuns.ExprOps {
  protected val trees: Trees
  import trees._

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
}
