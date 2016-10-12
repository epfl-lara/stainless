/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate
package imperative

import inox.ast.Identifier

trait Trees extends innerfuns.Trees { self =>

  /* XLang imperative trees to desugar */

  /** $encodingof `{ expr1; expr2; ...; exprn; last }` */
  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = if (exprs.forall(_.isTyped)) last.getType else Untyped
  }

  /** $encoding of `var vd = value; body` */
  case class LetVar(vd: ValDef, value: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (s.isSubtypeOf(value.getType, vd.tpe)) body.getType
      else Untyped
    }
  }

  /** $encodingof `vd = value` */
  case class Assignment(v: Variable, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = if (s.isSubtypeOf(value.getType, v.tpe)) {
      UnitType
    } else {
      Untyped
    }
  }

  /** $encodingof `obj.selector = value` */
  case class FieldAssignment(obj: Expr, selector: Identifier, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      def fromConstr(tp: TypedADTConstructor): Option[Type] = {
        tp.fields
          .find(_.id == selector)
          .filter(vd => s.isSubtypeOf(value.getType, vd.tpe))
          .map(_ => UnitType)
      }

      obj.getType match {
        case ct: ADTType => (ct.lookupADT.get match {
          case at: TypedADTSort =>
            at.constructors.flatMap(fromConstr)
          case ac: TypedADTConstructor =>
            fromConstr(ac).toSeq
        }).headOption.getOrElse(Untyped)

        case _ => Untyped
      }
    }
  }

  /** $encodingof `(while(cond) { ... }) invariant (pred)` */
  case class While(cond: Expr, body: Expr, pred: Option[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type =
      if (cond.getType == BooleanType && body.isTyped && pred.forall(_.getType == BooleanType)) UnitType
      else Untyped
  }

  /** $encodingof `array(index) = value` */
  case class ArrayUpdate(array: Expr, index: Expr, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type) if s.isSubtypeOf(value.getType, base) => UnitType
      case _ => Untyped
    }
  }


  class VarDef(id: Identifier, tpe: Type) extends ValDef(id, tpe) {
    override val flags: Set[Flag] = Set(IsVar)
  }

  object VarDef {
    def apply(id: Identifier, tpe: Type): VarDef = new VarDef(id, tpe)
    def unapply(d: Definition): Option[(Identifier, Type)] = d match {
      case vd: ValDef if vd.flags(IsVar) => Some(vd.id -> vd.tpe)
      case _ => None
    }
  }

  implicit def convertToVar = new VariableConverter[VarDef] {
    def convert(vs: VariableSymbol): VarDef = vs match {
      case vd: VarDef => vd
      case _ => VarDef(vs.id, vs.tpe)
    }
  }

  implicit class VariableSymbolToVar(vs: VariableSymbol) {
    def toVar: VarDef = vs.to[VarDef]
  }

  case object IsVar extends Flag("var", Seq.empty)

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps

  override val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  } = new TreeDeconstructor {
    protected val s: self.type = self
    protected val t: self.type = self
  }
}


trait TreeDeconstructor extends innerfuns.TreeDeconstructor {
  import inox.ast.Identifier

  protected val s: Trees
  protected val t: Trees

  override def deconstruct(vd: s.Definition): (Identifier, Seq[s.Expr], Seq[s.Type], (Identifier, Seq[t.Expr], Seq[t.Type]) => t.Definition) = vd match {
    case s.VarDef(id, tpe) => (id, Seq.empty, Seq(tpe), (id, _, tps) => t.VarDef(id, tps.head))
    case _ => super.deconstruct(vd)
  }

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {

    case s.Block(exprs, last) =>
      (Seq(), exprs :+ last, Seq(), (_, es, _) => t.Block(es.init, es.last))

    case s.LetVar(vd, value, expr) =>
      (Seq(vd.toVariable), Seq(value, expr), Seq(), (vs, es, _) => t.LetVar(vs.head.toVal, es(0), es(1)))

    case s.Assignment(v, value) =>
      (Seq(v), Seq(value), Seq(), (vs, es, _) => t.Assignment(vs.head, es.head))

    case s.FieldAssignment(obj, selector, value) =>
      (Seq(), Seq(obj, value), Seq(), (_, es, _) => t.FieldAssignment(es(0), selector, es(1)))

    case s.While(cond, body, pred) =>
      (Seq(), Seq(cond, body) ++ pred, Seq(), (_, es, _) => t.While(es(0), es(1), es.drop(2).headOption))

    case s.ArrayUpdate(array, index, value) =>
      (Seq(), Seq(array, index, value), Seq(), (_, es, _) => t.ArrayUpdate(es(0), es(1), es(2)))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.IsVar => (Seq(), Seq(), (_, _) => t.IsVar)
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
        case es => Block(es.init, es.last)
      })
    case _ => None
  } (expr)
}
