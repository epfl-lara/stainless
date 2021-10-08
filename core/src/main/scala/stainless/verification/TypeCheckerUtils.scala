/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
import trees._

import TypeCheckerContext._

object TypeCheckerUtils {

  type StainlessVC = verification.VC[stainless.trees.type]
  def StainlessVC(condition: stainless.trees.Expr, fd: Identifier, kind: VCKind, satisfiability: Boolean): StainlessVC =
    verification.VC(stainless.trees)(condition, fd, kind, satisfiability)

  object UncheckedExpr {
    def unapply(e: Expr): Option[Expr] = e match {
      case Annotated(body, flags) if flags contains DropVCs => Some(body)
      case _ => None
    }
  }

  // The type Top as an abstraction for `ValueType(_)` which ignores the
  // underlying type, arbitrarily set to `UnitType` here
  object Top {
    def apply() = ValueType(UnitType())

    def unapply(t: Type): Boolean = t match {
      case ValueType(_) => true
      case _ => false
    }
  }

  // The type { b: Boolean | b }
  object TrueBoolean {
    def apply() = {
      val vd = ValDef.fresh("__b", BooleanType())
      RefinementType(vd, vd.toVariable)
    }

    def unapply(t: Type): Boolean = t match {
      case RefinementType(vd, prop) => prop == vd.toVariable
      case _ => false
    }
  }

  // The type { u: Unit | e }
  object Truth {
    def apply(e: Expr) = {
      val vd = ValDef.fresh("__u", UnitType())
      RefinementType(vd, e)
    }

    def unapply(t: Type): Option[Expr] = t match {
      case RefinementType(vd, e) if vd.tpe == UnitType() => Some(e)
      case _ => None
    }

    def unapply(v: Variable): Option[Expr] = unapply(v.tpe)
  }

  // The type { letWitness: Unit | e1 == e2 }
  object LetEquality {
    def apply(e1: Variable, e2: Expr) = {
      val vd = ValDef.fresh(letWitness, UnitType())
      RefinementType(vd, Equals(e1, e2))
    }

    def unapply(t: Type): Option[(Variable, Expr)] = t match {
      case RefinementType(vd, Equals(e1: Variable,e2)) if vd.tpe == UnitType() && vd.id.name == letWitness => Some((e1, e2))
      case _ => None
    }

    def unapply(v: Variable): Option[(Variable, Expr)] = unapply(v.tpe)
  }

  def substVar(expr: Expr, id: Identifier, replacement: Expr): Expr = {
    new ConcreteStainlessSelfTreeTransformer {
      override def transform(e: Expr) = e match {
        case Variable(id2, _, _) if id2 == id => replacement
        case _ => super.transform(e)
      }
    }.transform(expr)
  }

  // TODO: implement ite for more types (PiType, SigmaType, etc.)
  def ite(b: Expr, t1: Type, t2: Type)(using opts: PrinterOptions, ctx: inox.Context): Type = (t1, t2) match {
    case _ if (t1 == t2) => t1

    case (RefinementType(vd1, prop1), RefinementType(vd2, prop2)) =>
      val newType = ite(b, vd1.tpe, vd2.tpe)
      val vd = ValDef.fresh(vd1.id.name, newType)
      val newProp1 = substVar(prop1, vd1.id, vd.toVariable)
      val newProp2 = substVar(prop2, vd2.id, vd.toVariable)
      RefinementType(vd, IfExpr(b, newProp1, newProp2))

    case (RefinementType(vd1, prop1), _) if (vd1.tpe == t2) =>
      RefinementType(vd1, Implies(b, prop1))
    case (_, RefinementType(vd2, prop2)) if (vd2.tpe == t1) =>
      RefinementType(vd2, Or(b, prop2))

    case (TupleType(tps1), TupleType(tps2)) =>
      TupleType(tps1.zip(tps2).map { case (t1, t2) => ite(b, t1, t2) })

    case (SetType(base1), SetType(base2)) =>
      SetType(ite(b, base1, base2))

    case (ADTType(id1, tps1), ADTType(id2, tps2)) if id1 == id2 =>
      ADTType(id1, tps1.zip(tps2).map { case (t1, t2) => ite(b, t1, t2) })

    case _ =>
      ctx.reporter.fatalError(b.getPos, s"The `If Then Else` type is not defined for types ${t1.asString} and ${t2.asString}")
  }

  // def lets(vds: Seq[ValDef], es: Seq[Expr], expr: Expr): Expr = {
  //   vds.zip(es).foldLeft(expr) { case (acc, (vd, e)) => Let(vd, e, acc) }
  // }

  def freshLets(vds: Seq[ValDef], es: Seq[Expr], expr: Expr)(using opts: PrinterOptions, ctx: inox.Context): Expr = {
    vds.zip(es).foldRight(expr, new Substituter(Map())) {
      case ((vd, e), (acc, freshener)) =>
        val substVd = freshener.transform(vd)
        val freshVd = substVd.freshen
        if (substVd.id != vd.id) {
          ctx.reporter.internalError(s"The freshener should not affect ${substVd.id.asString}.")
        }
        val newFreshener = freshener.enrich(vd.id, freshVd.id)
        (Let(freshVd, e, newFreshener.transform(acc)), newFreshener)
    }._1
  }

  // def insertLets(vds: Seq[ValDef], es: Seq[Expr], t: Type): Type = {
  //   new SelfTreeTransformer {
  //     override def transform(e: Expr) = lets(vds, es, e)
  //   }.transform(t)
  // }

  def insertFreshLets(vds: Seq[ValDef], es: Seq[Expr], t: Type)(using opts: PrinterOptions, ctx: inox.Context): Type = {
    new ConcreteStainlessSelfTreeTransformer {
      override def transform(e: Expr) = freshLets(vds, es, e)
    }.transform(t)
  }

  def shortString(s: String, maxWidth: Int = 160): String = {
    val r = s.replaceAll("\n", " ")
    if (r.length > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  def stripRefinementsAndAnnotations(t: Type): Type = t match {
    case RefinementType(vd, _) => stripRefinementsAndAnnotations(vd.tpe)
    case AnnotatedType(tpe, _) => stripRefinementsAndAnnotations(tpe)
    case _ => t
  }

  def pp(v: Variable)(using PrinterOptions): String = v.tpe match {
    case Truth(e) => e.asString
    case _ => v.asString + ": " + v.tpe.asString
  }

  def isArithmeticType(t: Type): Boolean = t match {
    case IntegerType() => true
    case RealType() => true
    case BVType(_, _) => true
    case _ => false
  }

  def isComparableType(t: Type): Boolean = t match {
    case IntegerType() => true
    case CharType() => true
    case RealType() => true
    case BVType(_, _) => true
    case _ => false
  }

  def lessThan(tpe: Type, e1: Expr, e2: Expr)(using ctx: inox.Context, opts: PrinterOptions): Expr = (tpe match {
    case IntegerType() => LessThan(e1, e2)
    case BVType(_, _) => LessThan(e1, e2)
    case TupleType(tps) =>
      or((1 to tps.length).map(i =>
        And(
          and((1 to i-1).map(j =>
            Equals(TupleSelect(e1,j), TupleSelect(e2,j))
          ): _*),
          lessThan(tps(i-1),TupleSelect(e1,i),TupleSelect(e2,i))
        )
      ): _*)
    case RefinementType(vd, ref) => lessThan(vd.tpe, e1, e2)
    case _ =>
      ctx.reporter.fatalError(e2.getPos, s"Type ${tpe.asString} is not supported for measures")
  }).setPos(e1)

  def positive(tpe: Type, e: Expr)(using ctx: inox.Context, opts: PrinterOptions): Expr = (tpe match {
    case IntegerType() => GreaterEquals(e, IntegerLiteral(0))
    case BVType(signed, size) => GreaterEquals(e, BVLiteral(signed, 0, size))
    case TupleType(tps) => and((1 to tps.length).map(i => positive(tps(i-1), TupleSelect(e,i))): _*)
    case RefinementType(vd, ref) => positive(vd.tpe, e)
    case _ =>
      ctx.reporter.fatalError(e.getPos, s"Type ${tpe.asString} is not supported for measures")
  }).setPos(e)

  case class Substituter(subst: Map[Identifier, Identifier]) extends ConcreteStainlessSelfTreeTransformer {
    override def transform(id: Identifier) = subst.getOrElse(id, id)
    def transformTp(tp: TypeParameter): TypeParameter = transform(tp).asInstanceOf[TypeParameter]
    def enrich(id1: Identifier, id2: Identifier): Substituter = {
      require(!subst.contains(id1))
      Substituter(subst + (id1 -> id2))
    }
    def enrich(m: Map[Identifier, Identifier]): Substituter = {
      require(m.forall { case (id,_) => !subst.contains(id) })
      Substituter(subst ++ m)
    }
    def contains(id: Identifier) = subst.contains(id)
  }

  def pred(e: Expr) = Minus(e, IntegerLiteral(1))
}
