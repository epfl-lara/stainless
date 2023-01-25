package stainless
package transformers
package lattices

import inox.solvers

trait Definitions {
  val trees: ast.Trees
  val symbols: trees.Symbols

  import trees._
  import symbols.{given, _}

  // If we do a summon[Ordering[Int]] within Opaques, it loops...
  private val intOrdering = summon[Ordering[Int]]

  object Opaques {
    // These opaques are defined here to avoid accidental conversion from Int to Code, etc.
    opaque type Code = Int

    object Code {
      def fromInt(i: Int): Code = i
    }

    opaque type VarId = Int

    object VarId {
      def fromInt(i: Int): VarId = i
    }

    given Ordering[Code] = intOrdering
    given Ordering[VarId] = intOrdering
  }
  import Opaques.{given, _}

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  enum Label {
    case Var(v: VarId)
    case Let
    case Tuple
    case ADT(id: Identifier, tps: Seq[Type])
    case ADTSelector(adt: ADTType, ctor: TypedADTConstructor, selector: Identifier)
    case FunctionInvocation(id: Identifier, tps: Seq[Type])
    case Annotated(flags: Seq[Flag])
    case IsConstructor(adt: ADTType, id: Identifier)

    case Assume
    case Assert
    case Require
    case Ensuring
    case Decreases

    case MatchExpr(patterns: Seq[LabelledPattern])
    case Passes(patterns: Seq[LabelledPattern])
    case IfExpr
    case Application
    case Lambda(params: Seq[VarId])
    case Choose(v: VarId)
    case Forall(params: Seq[VarId])

    case Or
    case Not

    case Equals
    case LessThan
    case GreaterThan
    case LessEquals
    case GreaterEquals

    case UMinus
    case Plus
    case Minus
    case Times
    case Division
    case Remainder
    case Modulo

    case BVNot
    case BVAnd
    case BVOr
    case BVXor
    case BVShiftLeft
    case BVAShiftRight
    case BVLShiftRight
    case BVNarrowingCast(newType: BVType)
    case BVWideningCast(newType: BVType)
    case BVUnsignedToSigned
    case BVSignedToUnsigned

    case Lit[T](lit: Literal[T])

    case TupleSelect(index: Int)

    case StringConcat
    case SubString
    case StringLength

    case FiniteSet(base: Type)
    case SetAdd
    case ElementOfSet
    case SubsetOf
    case SetIntersection
    case SetUnion
    case SetDifference

    case FiniteBag(base: Type)
    case BagAdd
    case MultiplicityInBag
    case BagIntersection
    case BagUnion
    case BagDifference

    case FiniteMap(keyTpe: Type, valueTpe: Type)
    case MapApply
    case MapUpdated
    case MapMerge

    case FiniteArray(base: Type)
    case LargeArray(elemsIndices: Seq[Int], base: Type)
    case ArraySelect
    case ArrayUpdated
    case ArrayLength

    case Error(tpe: Type, description: String)
    case NoTree(tpe: Type)

    def isLambda: Boolean = this match {
      case Lambda(_) => true
      case _ => false
    }

    def isEnsuring: Boolean = this match {
      case Ensuring => true
      case _ => false
    }

    def isLambdaLike: Boolean = this match {
      case _: Label.LambdaLike => true
      case _ => false
    }

    def isDecreases: Boolean = this match {
      case Decreases => true
      case _ => false
    }

    def isOr: Boolean = this match {
      case Or => true
      case _ => false
    }

    def isLiteral: Boolean = this match {
      case Lit(_) => true
      case _ => false
    }

    def isUnitLiteral: Boolean = this match {
      case Lit(UnitLiteral()) => true
      case _ => false
    }

    def isLitOrVar: Boolean = this match {
      case Lit(_) | Var(_) => true
      case _ => false
    }

    def isVar: Boolean = this match {
      case Var(_) => true
      case _ => false
    }

    def isIfExpr: Boolean = this match {
      case IfExpr => true
      case _ => false
    }

    lazy val hc: Int = java.util.Objects.hash(this.ordinal)
    override def hashCode(): Int = hc
  }
  object Label {
    type AssumeLike = Label.Assume.type | Label.Assert.type | Label.Require.type | Label.Decreases.type

    type LambdaLike = Label.Lambda | Label.Choose | Label.Forall

    type Rel = Label.Equals.type | Label.GreaterEquals.type | Label.GreaterThan.type | Label.LessEquals.type | Label.LessThan.type

    object LambdaLike {
      def unapply(l: LambdaLike): Seq[VarId] = l match {
        case Label.Lambda(vs) => vs
        case Label.Choose(v) => Seq(v)
        case Label.Forall(vs) => vs
      }
    }

    extension (l: LambdaLike) {
      def map(f: VarId => VarId) = l match {
        case Label.Lambda(vs) => Label.Lambda(vs.map(f))
        case Label.Choose(v) => Label.Choose(f(v))
        case Label.Forall(vs) => Label.Forall(vs.map(f))
      }
      def params: Seq[VarId] = LambdaLike.unapply(l)
      def replacedParams(newParams: Seq[VarId]): LambdaLike = l match {
        case Label.Lambda(old) =>
          assert(old.size == newParams.size)
          Label.Lambda(newParams)
        case Label.Choose(_) =>
          assert(newParams.size == 1)
          Label.Choose(newParams.head)
        case Label.Forall(old) =>
          assert(old.size == newParams.size)
          Label.Forall(newParams)
      }
    }
  }

  case class Signature(label: Label, children: Seq[Code]) {
    lazy val hc: Int = java.util.Objects.hash(label, children)
    override def hashCode(): Int = hc
  }

  enum LabelledPattern {
    case Wildcard extends LabelledPattern
    case ADT(id: Identifier, tps: Seq[Type], sub: Seq[LabelledPattern]) extends LabelledPattern
    case TuplePattern(sub: Seq[LabelledPattern]) extends LabelledPattern
    case Lit[T](lit: Literal[T]) extends LabelledPattern
    case Unapply(recs: Seq[Code], id: Identifier, tps: Seq[Type], sub: Seq[LabelledPattern]) extends LabelledPattern

    import LabelledPattern._
    def allPatterns: Seq[LabelledPattern] = Seq(this) ++ (this match {
      case Wildcard => Seq.empty
      case ADT(_, _, sub) => sub.flatMap(_.allPatterns)
      case TuplePattern(sub) => sub.flatMap(_.allPatterns)
      case Lit(_) => Seq.empty
      case Unapply(_, _, _, sub) => sub.flatMap(_.allPatterns)
    })
  }

  case class LabMatchCase(pattern: LabelledPattern, guard: Code, rhs: Code)

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  enum Purity {
    case Pure
    case Impure
    case Delayed(blockers: Set[Identifier])

    def ++(that: => Purity): Purity = {
      if (this == Impure) Impure
      else (this, that) match {
        case (Pure, Pure) => Pure
        case (Delayed(s1), Delayed(s2)) => Delayed(s1 ++ s2)
        case (Delayed(s1), Pure) => Delayed(s1)
        case (Pure, Delayed(s2)) => Delayed(s2)
        case _ => Impure
      }
    }

    def isPure: Boolean = this match {
      case Pure => true
      case _ => false
    }
  }

  object Purity {
    def fold(xs: Seq[Purity]): Purity = xs.foldLeft(Pure)(_ ++ _)
    def fromBoolean(isPure: Boolean): Purity = if (isPure) Pure else Impure
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  final def mkVar(v: VarId): Signature = Signature(Label.Var(v), Seq.empty)
  final def mkLet(e: Code, body: Code): Signature = Signature(Label.Let, Seq(e, body))
  final def mkTuple(args: Seq[Code]): Signature = {
    assert(args.size >= 2)
    Signature(Label.Tuple, args)
  }
  final def mkADT(id: Identifier, tps: Seq[Type], args: Seq[Code]): Signature = Signature(Label.ADT(id, tps), args)
  final def mkADTSelector(recv: Code, adt: ADTType, ctor: TypedADTConstructor, selector: Identifier): Signature = Signature(Label.ADTSelector(adt, ctor, selector), Seq(recv))
  final def mkFunInvoc(id: Identifier, tps: Seq[Type], args: Seq[Code]): Signature = Signature(Label.FunctionInvocation(id, tps), args)
  final def mkAnnot(e: Code, flags: Seq[Flag]): Signature = Signature(Label.Annotated(flags), Seq(e))
  final def mkIsCtor(e: Code, adt: ADTType, id: Identifier): Signature = Signature(Label.IsConstructor(adt, id), Seq(e))
  final def mkAssume(pred: Code, body: Code): Signature = Signature(Label.Assume, Seq(pred, body))
  final def mkAssert(pred: Code, body: Code): Signature = Signature(Label.Assert, Seq(pred, body))
  final def mkRequire(pred: Code, body: Code): Signature = Signature(Label.Require, Seq(pred, body))
  final def mkEnsuring(body: Code, pred: Code): Signature = Signature(Label.Ensuring, Seq(body, pred))
  final def mkDecreases(measure: Code, body: Code): Signature = Signature(Label.Decreases, Seq(measure, body))
  final def mkMatchExpr(scrut: Code, cases: Seq[LabMatchCase]): Signature = {
    assert(cases.nonEmpty)
    val (pats, guards, rhs) = cases.map(mc => (mc.pattern, mc.guard, mc.rhs)).unzip3
    Signature(Label.MatchExpr(pats), scrut +: guards.zip(rhs).flatMap((g, r) => Seq(g, r)))
  }
  final def mkPasses(scrut: Code, cases: Seq[LabMatchCase]): Signature = {
    assert(cases.nonEmpty)
    val (pats, guards, rhs) = cases.map(mc => (mc.pattern, mc.guard, mc.rhs)).unzip3
    Signature(Label.Passes(pats), scrut +: guards.zip(rhs).flatMap((g, r) => Seq(g, r)))
  }
  final def mkIfExpr(cond: Code, thn: Code, els: Code): Signature = Signature(Label.IfExpr, Seq(cond, thn, els))
  final def mkApp(callee: Code, args: Seq[Code]): Signature = Signature(Label.Application, callee +: args)
  final def mkLambda(params: Seq[VarId], body: Code): Signature = Signature(Label.Lambda(params), Seq(body))
  final def mkWickedChoose(v: VarId, pred: Code): Signature = Signature(Label.Choose(v), Seq(pred))
  final def mkForall(params: Seq[VarId], pred: Code): Signature = Signature(Label.Forall(params), Seq(pred))
  final def mkOr(es: Seq[Code]): Signature = {
    assert(es.size >= 2)
    Signature(Label.Or, es)
  }
  final def mkNot(e: Code): Signature = Signature(Label.Not, Seq(e))
  final def mkEquals(e1: Code, e2: Code): Signature = Signature(Label.Equals, Seq(e1, e2))
  final def mkLessThan(e1: Code, e2: Code): Signature = Signature(Label.LessThan, Seq(e1, e2))
  final def mkGreaterThan(e1: Code, e2: Code): Signature = Signature(Label.GreaterThan, Seq(e1, e2))
  final def mkLessEquals(e1: Code, e2: Code): Signature = Signature(Label.LessEquals, Seq(e1, e2))
  final def mkGreaterEquals(e1: Code, e2: Code): Signature = Signature(Label.GreaterEquals, Seq(e1, e2))
  final def mkUMinus(e: Code): Signature = Signature(Label.UMinus, Seq(e))
  final def mkPlus(cs: Seq[Code]): Signature = {
    assert(cs.size >= 2)
    Signature(Label.Plus, cs)
  }
  final def mkPlus(e1: Code, e2: Code): Signature = Signature(Label.Plus, Seq(e1, e2))
  final def mkMinus(e1: Code, e2: Code): Signature = Signature(Label.Minus, Seq(e1, e2))
  final def mkTimes(cs: Seq[Code]): Signature = {
    assert(cs.size >= 2)
    Signature(Label.Times, cs)
  }
  final def mkTimes(e1: Code, e2: Code): Signature = Signature(Label.Times, Seq(e1, e2))
  final def mkDivision(e1: Code, e2: Code): Signature = Signature(Label.Division, Seq(e1, e2))
  final def mkRemainder(e1: Code, e2: Code): Signature = Signature(Label.Remainder, Seq(e1, e2))
  final def mkModulo(e1: Code, e2: Code): Signature = Signature(Label.Modulo, Seq(e1, e2))
  final def mkBVNot(e: Code): Signature = Signature(Label.BVNot, Seq(e))
  final def mkBVAnd(e1: Code, e2: Code): Signature = Signature(Label.BVAnd, Seq(e1, e2))
  final def mkBVOr(e1: Code, e2: Code): Signature = Signature(Label.BVOr, Seq(e1, e2))
  final def mkBVXor(e1: Code, e2: Code): Signature = Signature(Label.BVXor, Seq(e1, e2))
  final def mkBVShiftLeft(e1: Code, e2: Code): Signature = Signature(Label.BVShiftLeft, Seq(e1, e2))
  final def mkBVAShiftRight(e1: Code, e2: Code): Signature = Signature(Label.BVAShiftRight, Seq(e1, e2))
  final def mkBVLShiftRight(e1: Code, e2: Code): Signature = Signature(Label.BVLShiftRight, Seq(e1, e2))
  final def mkBVNarrowingCast(e: Code, newType: BVType): Signature = Signature(Label.BVNarrowingCast(newType), Seq(e))
  final def mkBVWideningCast(e: Code, newType: BVType): Signature = Signature(Label.BVWideningCast(newType), Seq(e))
  final def mkBVUnsignedToSigned(e: Code): Signature = Signature(Label.BVUnsignedToSigned, Seq(e))
  final def mkBVSignedToUnsigned(e: Code): Signature = Signature(Label.BVSignedToUnsigned, Seq(e))
  final def mkLit[T](l: Literal[T]): Signature = Signature(Label.Lit(l), Seq.empty)
  final def mkTupleSelect(recv: Code, i: Int): Signature = Signature(Label.TupleSelect(i), Seq(recv))
  final def mkFiniteSet(elems: Seq[Code], base: Type): Signature = Signature(Label.FiniteSet(base), elems)
  final def mkSetAdd(set: Code, elem: Code): Signature = Signature(Label.SetAdd, Seq(set, elem))
  final def mkElementOfSet(elem: Code, set: Code): Signature = Signature(Label.ElementOfSet, Seq(elem, set))
  final def mkSubsetOf(lhs: Code, rhs: Code): Signature = Signature(Label.SubsetOf, Seq(lhs, rhs))
  final def mkSetIntersection(lhs: Code, rhs: Code): Signature = Signature(Label.SetIntersection, Seq(lhs, rhs))
  final def mkSetUnion(lhs: Code, rhs: Code): Signature = Signature(Label.SetUnion, Seq(lhs, rhs))
  final def mkSetDifference(lhs: Code, rhs: Code): Signature = Signature(Label.SetDifference, Seq(lhs, rhs))

  final def mkFiniteArray(elems: Seq[Code], base: Type): Signature = Signature(Label.FiniteArray(base), elems)
  final def mkLargeArray(elems: Map[Int, Code], default: Code, size: Code, base: Type): Signature = {
    val (elemsIndices, elemsCodes) = elems.toSeq.sortBy(_._1).unzip
    Signature(Label.LargeArray(elemsIndices, base), elemsCodes ++ Seq(default, size))
  }
  final def mkArraySelect(arr: Code, i: Code): Signature = Signature(Label.ArraySelect, Seq(arr, i))
  final def mkArrayUpdated(arr: Code, i: Code, v: Code): Signature = Signature(Label.ArrayUpdated, Seq(arr, i, v))
  final def mkArrayLength(arr: Code): Signature = Signature(Label.ArrayLength, Seq(arr))

  final def mkStringConcat(lhs: Code, rhs: Code): Signature = Signature(Label.StringConcat, Seq(lhs, rhs))
  final def mkSubString(expr: Code, start: Code, end: Code): Signature = Signature(Label.SubString, Seq(expr, start, end))
  final def mkStringLength(expr: Code): Signature = Signature(Label.StringLength, Seq(expr))

  final def mkFiniteBag(elems: Seq[(Code, Code)], base: Type): Signature =
    Signature(Label.FiniteBag(base), elems.flatMap { case (c1, c2) => Seq(c1, c2) })
  final def mkBagAdd(bag: Code, elem: Code): Signature = Signature(Label.BagAdd, Seq(bag, elem))
  final def mkMultiplicityInBag(elem: Code, bag: Code): Signature = Signature(Label.MultiplicityInBag, Seq(elem, bag))
  final def mkBagIntersection(lhs: Code, rhs: Code): Signature = Signature(Label.BagIntersection, Seq(lhs, rhs))
  final def mkBagUnion(lhs: Code, rhs: Code): Signature = Signature(Label.BagUnion, Seq(lhs, rhs))
  final def mkBagDifference(lhs: Code, rhs: Code): Signature = Signature(Label.BagDifference, Seq(lhs, rhs))

  final def mkFiniteMap(elems: Seq[(Code, Code)], default: Code, keyTpe: Type, valueTpe: Type): Signature =
    Signature(Label.FiniteMap(keyTpe, valueTpe),
      elems.flatMap { case (c1, c2) => Seq(c1, c2) } :+ default)
  final def mkMapApply(map: Code, key: Code): Signature = Signature(Label.MapApply, Seq(map, key))
  final def mkMapUpdated(map: Code, elem: Code, value: Code): Signature = Signature(Label.MapUpdated, Seq(map, elem, value))
  final def mkMapMerge(mask: Code, map1: Code, map2: Code): Signature = Signature(Label.MapMerge, Seq(mask, map1, map2))

  final def mkError(tpe: Type, description: String): Signature = Signature(Label.Error(tpe, description), Seq.empty)
  final def mkNoTree(tpe: Type): Signature = Signature(Label.NoTree(tpe), Seq.empty)

  final def mkAssumeLike(kind: Label.AssumeLike, pred: Code, body: Code): Signature = Signature(kind, Seq(pred, body))
  final def mkLambdaLike(kind: Label.LambdaLike, body: Code): Signature = Signature(kind, Seq(body))
}
