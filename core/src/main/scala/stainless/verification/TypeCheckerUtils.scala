/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package verification
import trees._

import TypeCheckerContext._

object TypeCheckerUtils {

  type StainlessVC = verification.VC[stainless.trees.type]

  class TypeCheckingException(val tree: inox.ast.Trees#Tree, val msg: String)
    extends Exception(msg)

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
      case RefinementType(vd, e) => Some(e)
      case _ => None
    }
  }

  // The type { u: Unit | e1 == e2 }
  object Equality {
    def apply(e1: Expr, e2: Expr) = {
      val vd = ValDef.fresh("__u", UnitType())
      RefinementType(vd, Equals(e1,e2))
    }

    def unapply(t: Type): Option[(Expr, Expr)] = t match {
      case RefinementType(vd, Equals(e1,e2)) if vd.tpe == UnitType() => Some((e1,e2))
      case _ => None
    }
  }

  // The type { letWitness: Unit | e1 == e2 }
  object LetEquality {
    def apply(e1: Variable, e2: Expr) = {
      val vd = ValDef.fresh(letWitness, UnitType())
      RefinementType(vd, Equals(e1, e2))
    }

    def unapply(t: Type): Option[(Variable, Expr)] = t match {
      case RefinementType(vd, Equals(e1: Variable,e2)) if vd.tpe == UnitType() && vd.id.name == letWitness => Some((e1,e2))
      case _ => None
    }
  }

  def renameVar(e: Expr, id1: Identifier, id2: Identifier): Expr = {
    new SelfTreeTransformer {
      override def transform(e: Expr) = e match {
        case Variable(id, tpe, flags) if id == id1 => Variable(id2, transform(tpe), flags.map(transform))
        case _ => super.transform(e)
      }
    }.transform(e)
  }

  // TODO: implement ite for more types (PiType, SigmaType, etc.)
  def ite(b: Expr, t1: Type, t2: Type)(implicit opts: PrinterOptions): Type = (t1, t2) match {
    case _ if (t1 == t2) => t1

    case (RefinementType(vd1, prop1), RefinementType(vd2, prop2)) =>
      val newType = ite(b, vd1.tpe, vd2.tpe)
      val vd = ValDef.fresh(vd1.id.name, newType)
      val newProp1 = renameVar(prop1, vd1.id, vd.id)
      val newProp2 = renameVar(prop2, vd2.id, vd.id)
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
      throw new TypeCheckingException(b, s"The `If Then Else` type is not defined for types ${t1.asString} and ${t2.asString}")
  }

  // def lets(vds: Seq[ValDef], es: Seq[Expr], expr: Expr): Expr = {
  //   vds.zip(es).foldLeft(expr) { case (acc, (vd, e)) => Let(vd, e, acc) }
  // }

  def freshLets(vds: Seq[ValDef], es: Seq[Expr], expr: Expr)(implicit opts: PrinterOptions, ctx: inox.Context): Expr = {
    vds.zip(es).foldRight(expr, new Freshener(Map())) {
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

  def insertFreshLets(vds: Seq[ValDef], es: Seq[Expr], t: Type)(implicit opts: PrinterOptions, ctx: inox.Context): Type = {
    new SelfTreeTransformer {
      override def transform(e: Expr) = freshLets(vds, es, e)
    }.transform(t)
  }

  def shortString(s: String, maxWidth: Int = 160): String = {
    val r = s.replaceAll("\n", " ")
    if (r.length > maxWidth) r.take(maxWidth - 3) + "..."
    else r
  }

  def simplifyAssertions(expr: Expr): Expr = {
    exprOps.postMap {
      case Assert(_, _, e) => Some(e)
      case Annotated(e, Seq(Unchecked)) => Some(e)
      case _ => None
    }(expr)
  }

  def stripRefinementsAndAnnotations(t: Type): Type = t match {
    case RefinementType(vd, _) => stripRefinementsAndAnnotations(vd.tpe)
    case AnnotatedType(tpe, _) => stripRefinementsAndAnnotations(tpe)
    case _ => t
  }

  def pp(v: Variable)(implicit opts: PrinterOptions): String = v.tpe match {
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

  def lessThan(tpe: Type, e1: Expr, e2: Expr)(implicit opts: PrinterOptions): Expr = (tpe match {
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
    case _ =>
      throw new TypeCheckingException(e2, s"Type ${tpe.asString} is not supported for measures")
  }).setPos(e1)

  def positive(tpe: Type, e: Expr)(implicit opts: PrinterOptions): Expr = (tpe match {
    case IntegerType() => GreaterEquals(e, IntegerLiteral(0))
    case BVType(signed, size) => GreaterEquals(e, BVLiteral(signed, 0, size))
    case TupleType(tps) => and((1 to tps.length).map(i => positive(tps(i-1), TupleSelect(e,i))): _*)
    case _ =>
      throw new TypeCheckingException(e, s"Type ${tpe.asString} is not supported for measures")
  }).setPos(e)

  case class Freshener(subst: Map[Identifier, Identifier]) extends SelfTreeTransformer {
    override def transform(id: Identifier) = subst.getOrElse(id, id)
    def transformTp(tp: TypeParameter): TypeParameter = transform(tp).asInstanceOf[TypeParameter]
    // def freshenVd(vd: ValDef): ValDef = transform(vd)
    // def freshenType(tpe: Type): Type = transform(tpe)
    // def freshenExpr(e: Expr): Expr = transform(e)
    def enrich(id1: Identifier, id2: Identifier): Freshener = {
      require(!subst.contains(id1))
      Freshener(subst + (id1 -> id2))
    }
    def enrich(m: Map[Identifier, Identifier]): Freshener = {
      require(m.forall { case (id,_) => !subst.contains(id) })
      Freshener(subst ++ m)
    }
    def contains(id: Identifier) = subst.contains(id)
  }

  // // Predecessor function defined on strictly positive integers
  // val predId = ast.SymbolIdentifier("pred")
  // val positiveVd = ValDef(FreshIdentifier("x"), IntegerType())
  // val positiveType = RefinementType(positiveVd, GreaterThan(positiveVd.toVariable, IntegerLiteral(0)))
  // val predArg = ValDef(FreshIdentifier("x"), positiveType)
  // val predBody: Expr = Minus(predArg.toVariable, IntegerLiteral(1))
  // val predFd = new FunDef(
  //   predId,
  //   Seq(),
  //   Seq(predArg),
  //   IntegerType(),
  //   predBody,
  //   Seq()
  // )
  // def pred(e: Expr) = FunctionInvocation(predId, Seq(), Seq(e))
  def pred(e: Expr) = Minus(e, IntegerLiteral(1))
}
