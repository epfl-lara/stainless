/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import inox.solvers.*
import TypeCheckerUtils.*
import TypeCheckerDerivation.*
import TypeCheckerContext.*
import stainless.termination.optCheckMeasures

import scala.collection.{immutable, mutable}

object DebugSectionTypeChecker extends inox.DebugSection("type-checker")
object DebugSectionTypeCheckerVCs extends inox.DebugSection("type-checker-vcs")
object DebugSectionDerivation extends inox.DebugSection("derivation")

import inox.utils.Position

trait VCFilter extends (StainlessVC => Boolean) { self =>
  def inverse: VCFilter = vc => !self(vc)
  def withEmitVCs(emit: Boolean): VCFilter =
    vc => emit || vc.kind.isMeasureRelated // We always emit VCs for measures, even under DropVCs
}

object VCFilter {
  val all: VCFilter  = vc => true
  val none: VCFilter = vc => false

  def only(kinds: VCKind*): VCFilter = {
    val set = kinds.toSet
    vc => set.contains(vc.kind)
  }

  def except(kinds: VCKind*): VCFilter = {
    val set = kinds.toSet
    vc => set.contains(vc.kind)
  }

  val measuresOnly: VCFilter = only(VCKind.MeasureDecreases, VCKind.MeasurePositive)
  val noMeasures: VCFilter   = measuresOnly.inverse

  def fromOptions(options: inox.Options): VCFilter = {
    import stainless.utils.YesNoOnly._

    options.findOptionOrDefault(optCheckMeasures) match {
      case Yes  => VCFilter.all
      case Only => VCFilter.measuresOnly
      case No   => VCFilter.noMeasures
    }
  }
}

class TypeChecker(val program: StainlessProgram, val context: inox.Context, val vcFilter: VCFilter) {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}
  import CallGraphOrderings.{given, _}

  given givenDebugSection: DebugSectionTypeChecker.type = DebugSectionTypeChecker

  val checkMeasures = options.findOptionOrDefault(optCheckMeasures)
  val checkSatPrecond = options.findOptionOrDefault(optSatPrecond)

  /* ====================================
   *     Polarity in ADT definitions
   * ==================================== */

  // We then use the paths to compute the polarity of each type parameter
  sealed abstract class Polarity {
    def >=(p: Polarity): Boolean
    def glb(p: Polarity): Polarity =
      if (this >= p) p
      else if (p >= this) this
      else Nothing
    def *(p: Polarity): Polarity
  }

  case object Unused extends Polarity {
    override def >=(p: Polarity) = true
    override def *(p: Polarity): Polarity = p
  }

  case object StrictlyPositive extends Polarity {
    override def >=(p: Polarity) = p ==  StrictlyPositive || p == Positive || p == Nothing
    def *(p: Polarity): Polarity = p match {
      case Unused => StrictlyPositive
      case _ => p
    }
  }

  case object Positive extends Polarity {
    override def >=(p: Polarity) = p == Positive || p == Nothing
    def *(p: Polarity): Polarity = p match {
      case Unused => Positive
      case StrictlyPositive => Positive
      case _ => p
    }
  }

  case object Negative extends Polarity {
    override def >=(p: Polarity) = p == Negative || p == Nothing
    def *(p: Polarity): Polarity = p match {
      case Unused => Negative
      case StrictlyPositive => Negative
      case Positive => Negative
      case Negative => Positive
      case Nothing => Nothing
    }
  }

  case object Nothing extends Polarity {
    override def >=(p: Polarity) = p == Nothing
    def *(p: Polarity): Polarity = Nothing
  }

  object Polarity {
    def apply(pols: Seq[Polarity]) = {
      pols.foldLeft(Unused: Polarity) { _ * _ }
    }
  }

  // For every ADT A (identifier), and type parameter T (identifier) of A,
  // paths((A,T)) registers (a set of) all possible paths to reach T in the
  // type definition of A.

  // A path is represented as a list of Edge's, where each Edge is either
  // a change of direction (NegationEdge that represents going to the left of
  // an arrow), a base parametric type (Set, Bag, ...), or the identifier
  // of a type parameter of an ADT

  // Example:
  // We are given an ADT B[X], and an ADT
  // A[T], with a constructor of type: Int => B[Set[T] -> Int]
  // The path to reach T here is:
  //   Seq(B.X, NegationEdge, SetEdge)
  //
  // We also use paths((A,B)) to register the paths to reach B in A


  // At the moment we supposed that base parametric types have a `Nothing`
  // polarity, meaning their type parameters are not covariant or contraviarant.
  // This could perhaps be relaxed
  sealed abstract class Edge {
    // polarities is mutable but `polarity` doesn't mutate it
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]): Polarity
  }

  case object NegationEdge extends Edge {
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]) = Negative
  }

  case object SetEdge extends Edge {
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]) = StrictlyPositive
  }

  case object BagEdge extends Edge {
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]) = Nothing
  }

  case object ArrayEdge extends Edge {
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]) = Nothing
  }

  case object MapLeftEdge extends Edge {
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]) = Nothing
  }

  case object MapRightEdge extends Edge {
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]) = Nothing
  }

  case class TypeParameterEdge(sortId: Identifier, tpId: Identifier) extends Edge {
    def polarity(polarities: mutable.Map[(Identifier,Identifier),Polarity]) = polarities((sortId, tpId))
  }

  var paths = collection.mutable.Map[(Identifier,Identifier),Set[Seq[Edge]]]()

  for ((id,sort) <- sorts) {
    for (cons <- sort.constructors) {
      for (vd <- cons.fields) {
        def explore(t: Type, currentPath: Seq[Edge]): Unit = t match {
          case UnitType() => ()
          case BooleanType() => ()
          case IntegerType() => ()
          case RealType() => ()
          case StringType() => ()
          case CharType() => ()
          case BVType(_, _) => ()

          case SetType(tpe) => explore(tpe, currentPath :+ SetEdge)
          case BagType(tpe) => explore(tpe, currentPath :+ BagEdge)
          case ArrayType(tpe) => explore(tpe, currentPath :+ ArrayEdge)
          case MapType(from, to) =>
            explore(from, currentPath :+ MapLeftEdge)
            explore(to, currentPath :+ MapRightEdge)

          case RefinementType(vd, prop) => explore(vd.tpe, currentPath)

          case FunctionType(ts, returnType) =>
            ts.map(tpe => explore(tpe, currentPath :+ NegationEdge))
            explore(returnType, currentPath)

          case PiType(params, returnType) =>
            params.map(vd => explore(vd.tpe, currentPath :+ NegationEdge))
            explore(returnType, currentPath)
          case SigmaType(params, returnType) =>
            params.map(vd => explore(vd.tpe, currentPath))
            explore(returnType, currentPath)
          case TupleType(types) =>
            types.map(tpe => explore(tpe, currentPath))

          case tp@TypeParameter(tpId, _) =>
            paths((id, tpId)) = paths.getOrElse((id, tpId), Set()) + currentPath

          case ADTType(id2, tps) =>
            paths((id, id2)) = paths.getOrElse((id, id2), Set()) + currentPath
            getSort(id2).tparams.zip(tps).map {
              case (tp, tpe) => explore(tpe, currentPath :+ TypeParameterEdge(id2, tp.id))
            }

          case RecursiveType(id2, tps, _) =>
            paths((id, id2)) = paths.getOrElse((id, id2), Set()) + currentPath
            getSort(id2).tparams.zip(tps).map {
              case (tp, tpe) => explore(tpe, currentPath :+ TypeParameterEdge(id2, tp.id))
            }

          case _ =>
            reporter.fatalError(t.getPos, s"Couldn't determine polarity of type ${t.asString}")
        }
        explore(vd.tpe, Seq())
      }
    }
  }

  // Initialization of polarities for every pair of ADTs (A, B), and for every
  // pair ADT (A,T) where T is a type parameter of A
  var polarities = collection.mutable.Map[(Identifier,Identifier), Polarity]()
  for ((id1, sort) <- sorts) {
    for (tp <- sort.tparams)
      polarities((id1,tp.id)) = Unused
    for (id2 <- sorts.keySet)
      polarities((id1,id2)) = Unused
  }

  var progress = true
  while (progress) {
    progress = false
    for (((id1, id2), ps) <- paths) {
      for (path <- ps) {
        val pol = Polarity(path.map(_.polarity(polarities)))
        val previousPolarity = polarities((id1,id2))
        val newPolarity = previousPolarity.glb(pol)
        if (previousPolarity != newPolarity) {
          polarities((id1,id2)) = newPolarity
          progress = true
        }
      }
    }
  }

  // At the moment, we reject every non-strictly positive ADT
  for ((id1,sort) <- sorts) {
    val deps = dependencies(id1)
    for (id2 <- sorts.keySet if id1 == id2 || (deps.contains(id2) && dependencies(id2).contains(id1))) {
      if (!(polarities((id1,id2)) >= StrictlyPositive))
        reporter.fatalError(sort.getPos, s"ADT ${id2.asString} must appear only in strictly positive positions of ${id1.asString}")
    }
  }


  /* ====================================
   *    Type checking helper functions
   * ==================================== */


  def checkTypes(tc: TypingContext, exprs: Seq[Expr], types: Seq[Type]): TyperResult = {
    exprs.zip(types).foldLeft(TyperResult.valid){
      case (tr, (e, tpe)) => tr ++ checkType(tc, e, tpe)
    }
  }

  def checkTypes(tc: TypingContext, exprs: Seq[Expr], tpe: Type): TyperResult = {
    checkTypes(tc, exprs, exprs.map(_ => tpe))
  }

  def areDependentTypes(tc: TypingContext, types: Seq[ValDef]): TyperResult = {
    types.foldLeft((tc, new Substituter(immutable.Map()), TyperResult.valid)) {
      case ((tcAcc, freshener, tr), vd) =>
        val freshVd = freshener.transform(vd)
        val (newTc, newId) = tcAcc.freshBind(freshVd)
        if (freshVd.id != vd.id)
          reporter.internalError("In `areDependentTypes', the freshener should not affect the id of the current `vd`.")
        (newTc, freshener.enrich(vd.id, newId), tr ++ isType(tcAcc, freshVd.tpe))
    }._3
  }

  def checkDependentTypes(tc: TypingContext, exprs: Seq[Expr], types: Seq[ValDef]): TyperResult = {
    exprs.zip(types).foldLeft((tc, new Substituter(immutable.Map()), TyperResult.valid)) {
      case ((tcAcc, freshener, tr), (e, vd)) =>
        val freshVd = freshener.transform(vd)
        val (newTc, newId) = tcAcc.freshBindWithValue(freshVd, e)
        if (freshVd.id != vd.id)
          reporter.internalError("In `checkDependentTypes', the freshener should not affect the id of the current `vd`.")
        (newTc, freshener.enrich(vd.id, newId), tr ++ checkType(tcAcc, e, freshVd.tpe))
    }._3
  }

  def areSubtypes(tc: TypingContext, types1: Seq[ValDef], types2: Seq[ValDef]): (TypingContext, Substituter, TyperResult) = {
    assert(types1.length == types2.length, "Function `areSubtypes` expects sequences of the same size")
    types1.zip(types2).foldLeft((tc, new Substituter(immutable.Map()), TyperResult.valid)) {
      case ((tcAcc, freshener, tr), (vd1, vd2)) =>
        val freshVd1 = freshener.transform(vd1)
        val freshVd2 = freshener.transform(vd2)
        if (freshVd1.id != vd1.id)
          reporter.internalError("In `areSubtypes', the freshener should not affect the id of the current `vd`.")
        if (freshVd2.id != vd2.id)
          reporter.internalError("In `areSubtypes', the freshener should not affect the id of the current `vd`.")
        val (newTc, newId) = tcAcc.freshBind(freshVd1)
        val newFreshener = freshener.enrich(collection.immutable.Map(vd1.id -> newId, vd2.id -> newId))
        (newTc, newFreshener, tr ++ isSubtype(tcAcc, freshVd1.tpe, freshVd2.tpe))
    }
  }

  def areSubtypes(tc: TypingContext, types1: Seq[Type], types2: Seq[Type]): TyperResult = {
    assert(types1.length == types2.length, "Function `areSubtypes` (non-dependent) expects sequences of the same size")
    TyperResult(types1.zip(types2).map { case (tp1, tp2) => isSubtype(tc, tp1, tp2) })
  }


  /* ====================================
   *         Type checking algorithm
   * ==================================== */

  /** The `isType` function checks that a type is well-formed in a given context,
    * and generates a sequence of verification conditions to be checked.
    * Otherwise, it emits a `TypeCheckingException`.
    */
  def isType(tc0: TypingContext, t: Type): TyperResult = {
    reporter.debug(s"\n${tc0.indent}Checking that: ${t.asString} (${t.getPos})")
    reporter.debug(s"${tc0.indent}is a type in context:")
    reporter.debug(tc0.asString(tc0.indent))
    val tc = tc0.inc()
    val res: TyperResult = t match {
      case UnitType() => TyperResult.valid
      case BooleanType() => TyperResult.valid
      case IntegerType() => TyperResult.valid
      case RealType() => TyperResult.valid
      case StringType() => TyperResult.valid
      case CharType() => TyperResult.valid
      case BVType(_, _) => TyperResult.valid

      case SetType(tpe) => isType(tc, tpe)
      case BagType(tpe) => isType(tc, tpe)
      case ArrayType(tpe) => isType(tc, tpe)
      case MapType(from, to) => isType(tc, from) ++ isType(tc, to)

      case AnnotatedType(tpe, _) => isType(tc, tpe)
      case RefinementType(vd, prop) =>
        val (tc2, id2) = tc.freshBind(vd)
        val freshProp: Expr = Substituter(immutable.Map(vd.id -> id2)).transform(prop)
        isType(tc, vd.tpe) ++ checkType(tc2, freshProp, BooleanType())

      case FunctionType(ts, returnType) =>
        TyperResult(ts.map(isType(tc, _))) ++ isType(tc, returnType)

      case PiType(params, returnType) =>
        areDependentTypes(tc, params) ++ isType(tc.bind(params), returnType)
      case SigmaType(params, returnType) =>
        areDependentTypes(tc, params) ++ isType(tc.bind(params), returnType)
      case TupleType(types) =>
        TyperResult(types.map(isType(tc, _)))

      case tp@TypeParameter(id, _) =>
        if (tc.typeVariables(tp)) TyperResult.valid
        else reporter.fatalError(t.getPos, s"Type variable ${id.asString} is not defined in context:\n${tc.asString()}")

      case ADTType(id, tps) =>
        if (tc.visibleADTs(id)) TyperResult(tps.map(isType(tc, _)))
        else reporter.fatalError(t.getPos, s"ADT ${id.asString} is not in context:\n${tc.asString()}")

      case RecursiveType(id, tps, e) =>
        if (tc.visibleADTs(id)) TyperResult(tps.map(isType(tc, _))) ++ checkType(tc, e, IntegerType())
        else reporter.fatalError(t.getPos, s"ADT ${id.asString} is not in context:\n${tc.asString()}")

      case _ =>
        reporter.fatalError(t.getPos, s"Could not check well-formedness of type: ${t.asString} (${t.getClass})\nin context:\n${tc.asString()}")
    }
    res.root(IsType(tc,t))
  }

  def inferOperationType(name: String, fullExpr: Expr, tc: TypingContext, allowedType: Type => Boolean, returnType: Option[Type], exprs: Expr*): (Type, TyperResult) = {
    require(exprs.size > 0)
    val (tpe, tr) = inferType(tc, exprs.head)
    val baseTpe = stripRefinementsAndAnnotations(tpe)
    if (allowedType(baseTpe)) {
      val tr2 = checkTypes(tc, exprs.tail, exprs.tail.map(_ => baseTpe))
      (returnType.getOrElse(baseTpe), tr ++ tr2)
    } else {
      reporter.fatalError(fullExpr.getPos, s"Cannot use `$name` on type: ${baseTpe.asString}\nin context:\n${tc.asString()}")
    }
  }

  /** Some recursive type operations
    * `index` add indices for ADTType's and transform them in RecursiveType's
    * indexed by `size`
    *
    * `baseType` returns the base type, corresponding to the unfolding of a
    * recursive type at index 0
    */
  def index(id: Identifier, t: Type, size: Expr): Type = {
    new ConcreteStainlessSelfTreeTransformer {
      override def transform(tpe: Type) = tpe match {
        // We replace occurrences of ADT's that are mutually recursive with `id` with their
        // indexed version
        case ADTType(sort, tps) if sort == id || dependencies(sort).contains(id) =>
          RecursiveType(sort, tps.map(transform), transform(size))
        case _ => super.transform(tpe)
      }
    }.transform(t)
  }

  def index(sort: Identifier, vd: ValDef, size: Expr): ValDef = {
    vd.copy(tpe = index(sort, vd.tpe, size)).setPos(vd)
  }

  def baseType(sort: Identifier, tpe: Type): Type = {
    tpe match {
      case TupleType(tps) => TupleType(tps.map(baseType(sort, _)))
      case _ =>
        val collector = symbols.getSortCollector
        collector.traverse(tpe)

        // If every sort `sort2` that appears in `tpe` does not depend on `sort`
        // we can return the same type
        if (collector.result.forall(sort2 => !symbols.dependencies(sort2).contains(sort))) tpe
        // Otherwise we return `ValueType` (which represents a form of Top type) to approximate
        else ValueType(tpe)
    }
  }

  def baseType(sort: Identifier, vd: ValDef): ValDef = {
    vd.copy(tpe = baseType(sort, vd.tpe)).setPos(vd)
  }

  /** The `inferType` function succeeds by returning a type for `e` and a
    * sequence of verification conditions to be checked. If it fails to infer a
    * type, it emits a `TypeCheckingException`.
    */
  def inferType(tc0: TypingContext, e: Expr): (Type, TyperResult) = {
    reporter.debug(s"\n${tc0.indent}Inferring type of: ${e.asString} (${e.getPos})")
    reporter.debug(s"${tc0.indent}in context:")
    reporter.debug(tc0.asString(tc0.indent))
    val tc = tc0.inc()
    val (t, tr): (Type, TyperResult) = e match {
      case UnitLiteral() => (UnitType(), TyperResult.valid)
      case BooleanLiteral(_) => (BooleanType(), TyperResult.valid)
      case IntegerLiteral(_) => (IntegerType(), TyperResult.valid)
      case StringLiteral(_) => (StringType(), TyperResult.valid)
      case CharLiteral(_) => (CharType(), TyperResult.valid)
      case FractionLiteral(_, _) => (RealType(), TyperResult.valid)
      case BVLiteral(signed, _, size) => (BVType(signed, size), TyperResult.valid)

      case UncheckedExpr(e) => inferType(tc.withEmitVCs(false), e)
      case Annotated(e, _) => inferType(tc, e)

      case NoTree(tpe) => (tpe, isType(tc, tpe))

      case Plus(lhs, rhs) => inferOperationType("plus", e, tc, isArithmeticType, None, lhs, rhs)
      case Minus(lhs, rhs) => inferOperationType("minus", e, tc, isArithmeticType, None, lhs, rhs)
      case UMinus(e2) => inferOperationType("uminus", e, tc, isArithmeticType, None, e2)
      case Times(lhs, rhs) => inferOperationType("times", e, tc, isArithmeticType, None, lhs, rhs)
      case Division(lhs, rhs) => inferOperationType("division", e, tc, isArithmeticType, None, lhs, rhs)

      case Remainder(lhs, rhs) => inferOperationType("remainer", e, tc, t => t.isInstanceOf[BVType] || t.isInstanceOf[IntegerType], None, lhs, rhs)
      case Modulo(lhs, rhs) => inferOperationType("modulo", e, tc, t => t.isInstanceOf[BVType] || t.isInstanceOf[IntegerType], None, lhs, rhs)

      case GreaterEquals(lhs, rhs) => inferOperationType(">=", e, tc, isComparableType, Some(BooleanType()), lhs, rhs)
      case LessEquals(lhs, rhs) => inferOperationType("<=", e, tc, isComparableType, Some(BooleanType()), lhs, rhs)
      case GreaterThan(lhs, rhs) => inferOperationType(">", e, tc, isComparableType, Some(BooleanType()), lhs, rhs)
      case LessThan(lhs, rhs) => inferOperationType("<", e, tc, isComparableType, Some(BooleanType()), lhs, rhs)

      case BVNot(e2) => inferOperationType("bvnot (~)", e, tc, _.isInstanceOf[BVType], None, e2)
      case BVAnd(lhs, rhs) => inferOperationType("bvand (&)", e, tc, _.isInstanceOf[BVType], None, lhs, rhs)
      case BVOr(lhs, rhs) => inferOperationType("bvor (|)", e, tc, _.isInstanceOf[BVType], None, lhs, rhs)
      case BVXor(lhs, rhs) => inferOperationType("bvxor", e, tc, _.isInstanceOf[BVType], None, lhs, rhs)
      case BVShiftLeft(lhs, rhs) => inferOperationType("bvshiftleft", e, tc, _.isInstanceOf[BVType], None, lhs, rhs)
      case BVAShiftRight(lhs, rhs) => inferOperationType("bvshiftright", e, tc, _.isInstanceOf[BVType], None, lhs, rhs)
      case BVLShiftRight(lhs, rhs) => inferOperationType("bvlshiftright", e, tc, _.isInstanceOf[BVType], None, lhs, rhs)

      case StringConcat(s1, s2) =>
        (StringType(), checkType(tc, s1, StringType()) ++ checkType(tc, s2, StringType()))
      case SubString(s, start, end) =>
        (StringType(),
          checkType(tc, s, StringType()) ++
          checkType(tc, start, IntegerType()) ++
          checkType(tc, end, IntegerType())
        )
      case StringLength(s) =>
        (IntegerType(), checkType(tc, s, StringType()))

      case c@BVWideningCast(e2, newType) =>
        val (tpe, vcs) = inferType(tc, e2)
        stripRefinementsAndAnnotations(tpe) match {
          case BVType(s, from) if s == newType.signed && from < newType.size => (newType, vcs)
          case _ => reporter.fatalError(e.getPos, s"Cannot widen boolean vector ${e2.asString} to ${newType.asString}")
        }

      case c@BVNarrowingCast(e2, newType) =>
        val (tpe, vcs) = inferType(tc, e2)
        stripRefinementsAndAnnotations(tpe) match {
          case BVType(s, from) if s == newType.signed && from > newType.size => (newType, vcs)
          case _ => reporter.fatalError(e.getPos, s"Cannot narrow boolean vector ${e2.asString} to ${newType.asString}")
        }

      case c@BVUnsignedToSigned(e2) =>
        val (tpe, vcs) = inferType(tc, e2)
        stripRefinementsAndAnnotations(tpe) match {
          case BVType(false, size) => (BVType(true, size), vcs)
          case _ => reporter.fatalError(e.getPos, s"Cannot use `toSigned` on ${e2.asString}")
        }
      case c@BVSignedToUnsigned(e2) =>
        val (tpe, vcs) = inferType(tc, e2)
        stripRefinementsAndAnnotations(tpe) match {
          case BVType(true, size) => (BVType(false, size), vcs)
          case _ => reporter.fatalError(e.getPos, s"Cannot use `toUnsigned` on ${e2.asString}")
        }

      case FiniteSet(elements, tpe) =>
        (SetType(tpe),
          if (elements.isEmpty) isType(tc, tpe)
          else checkTypes(tc, elements, elements.map(_ => tpe)))
      case SetUnion(s1, s2) => inferOperationType("union (++)", e, tc, _.isInstanceOf[SetType], None, s1, s2)
      case SetIntersection(s1, s2) => inferOperationType("intersection (&)", e, tc, _.isInstanceOf[SetType], None, s1, s2)
      case SetDifference(s1, s2) => inferOperationType("difference (\\\\)", e, tc, _.isInstanceOf[SetType], None, s1, s2)
      case SubsetOf(s1, s2) => inferOperationType("subsetOf", e, tc, _.isInstanceOf[SetType], Some(BooleanType()), s1, s2)
      case ElementOfSet(element, set) =>
        val (tpe, vcs) = inferType(tc, set)
        stripRefinementsAndAnnotations(tpe) match {
          case SetType(base) => (BooleanType(), checkType(tc, element, base))
          case _ => reporter.fatalError(set.getPos, s"Expected set type, but got ${tpe.asString}")
        }
      case SetAdd(bag, element) =>
        val (tpe, vcs) = inferType(tc, bag)
        stripRefinementsAndAnnotations(tpe) match {
          case t@SetType(base) => (t, checkType(tc, element, base))
          case _ => reporter.fatalError(bag.getPos, s"Expected set type, but got ${tpe.asString}")
        }

      case FiniteBag(elements, tpe) =>
        (BagType(tpe),
          if (elements.isEmpty) isType(tc, tpe)
          else
            checkTypes(tc, elements.map(_._1), elements.map(_ => tpe)) ++
            checkTypes(tc, elements.map(_._2), elements.map(_ => IntegerType()))
        )
      case BagUnion(s1, s2) => inferOperationType("bag union", e, tc, _.isInstanceOf[BagType], None, s1, s2)
      case BagIntersection(s1, s2) => inferOperationType("bag intersection", e, tc, _.isInstanceOf[BagType], None, s1, s2)
      case BagDifference(s1, s2) => inferOperationType("bag difference", e, tc, _.isInstanceOf[BagType], None, s1, s2)
      case MultiplicityInBag(element, bag) =>
        val (tpe, vcs) = inferType(tc, bag)
        stripRefinementsAndAnnotations(tpe) match {
          case BagType(base) => (IntegerType(), checkType(tc, element, base))
          case _ => reporter.fatalError(bag.getPos, s"Expected bag type, but got ${tpe.asString}")
        }
      case BagAdd(bag, element) =>
        val (tpe, vcs) = inferType(tc, bag)
        stripRefinementsAndAnnotations(tpe) match {
          case t@BagType(base) => (t, checkType(tc, element, base))
          case _ => reporter.fatalError(bag.getPos, s"Expected bag type, but got ${tpe.asString}")
        }

      case FiniteMap(pairs, default, from, to) =>
        (MapType(from, to),
          if (pairs.isEmpty) isType(tc, from) ++ isType(tc, to)
          else
            checkType(tc, default, to) ++
            checkTypes(tc, pairs.map(_._1), List.fill(pairs.size)(from)) ++
            checkTypes(tc, pairs.map(_._2), List.fill(pairs.size)(to))
        )
      case MapUpdated(m, k, v) =>
        val (tpe, vcs) = inferType(tc, m)
        stripRefinementsAndAnnotations(tpe) match {
          case t@MapType(from, to) => (t, vcs ++ checkType(tc, k, from) ++ checkType(tc, v, to))
          case _ => reporter.fatalError(m.getPos, s"Expected map type, but got ${tpe.asString}")
        }
      case MapMerge(mask, map1, map2) =>
        val (tpe, vcs) = inferType(tc, map1)
        stripRefinementsAndAnnotations(tpe) match {
          case t@MapType(from, to) => (t, vcs ++ checkType(tc, mask, SetType(from)) ++ checkType(tc, map2, t))
          case _ => reporter.fatalError(map1.getPos, s"Expected map type, but got ${tpe.asString}")
        }
      case MapApply(m, k) =>
        val (tpe, vcs) = inferType(tc, m)
        stripRefinementsAndAnnotations(tpe) match {
          case MapType(from, to) => (to, vcs ++ checkType(tc, k, from))
          case _ => reporter.fatalError(m.getPos, s"Expected map type, but got ${tpe.asString}")
        }

      case FiniteArray(elements, tpe) =>
        (ArrayType(tpe),
          if (elements.isEmpty) isType(tc, tpe)
          else checkTypes(tc, elements, tpe))
      case LargeArray(elements, default, size, tpe) =>
        (ArrayType(tpe),
          checkTypes(tc, elements.values.toSeq, tpe) ++
          checkType(tc, default, tpe) ++
          checkType(tc, size, Int32Type()))
      case ArrayLength(a) =>
        val (tpe, vcs) = inferType(tc, a)
        stripRefinementsAndAnnotations(tpe) match {
          case ArrayType(_) => (Int32Type(), vcs)
          case _ => reporter.fatalError(a.getPos, s"Expected array type, but got ${tpe.asString}")
        }
      case ArraySelect(a, i) =>
        val (tpe, vcs) = inferType(tc, a)
        stripRefinementsAndAnnotations(tpe) match {
          case ArrayType(base) => (base, vcs ++ checkType(tc, i, Int32Type()))
          case _ => reporter.fatalError(a.getPos, s"Expected array type, but got ${tpe.asString}")
        }
      case ArrayUpdated(a, i, v) =>
        val (tpe, vcs) = inferType(tc, a)
        stripRefinementsAndAnnotations(tpe) match {
          case t@ArrayType(base) => (t, vcs ++ checkType(tc, i, Int32Type()) ++ checkType(tc, v, base))
          case _ => reporter.fatalError(a.getPos, s"Expected array type, but got ${tpe.asString}")
        }

      case Tuple(es) =>
        val typesAndResults = es.map(e => inferType(tc, e))
        (TupleType(typesAndResults.map(_._1)), TyperResult(typesAndResults.map(_._2)))

      case TupleSelect(p, i) =>
        val (tpe, vcs) = inferType(tc, p)
        stripRefinementsAndAnnotations(tpe) match {
          case TupleType(ts) if (i <= ts.length) => (ts(i-1), vcs)
          case SigmaType(from, to) =>
            val binders = from.take(i-1)
            val returnType = (from.map(_.tpe) :+ to).toSeq(i-1)
            val previousElements = (1 to i-1).toSeq.map(j => TupleSelect(p,j))
            (insertFreshLets(binders, previousElements, returnType), vcs)
          case _ => reporter.fatalError(e.getPos,
            s"${tc0.currentFid.map(fid => "(In function " + fid + ")").mkString} Cannot use tuple selection on type ${tpe.asString} with index $i"
          )
        }

      case m: MatchExpr => inferType(tc, matchToIfThenElse(e, false))

      case IfExpr(b, e1, e2) =>
        val (tpe1, tr1) = inferType(tc.withTruth(b).withLastPos(e1), e1)
        val (tpe2, tr2) = inferType(tc.withTruth(Not(b)).withLastPos(e2), e2)
        (ite(b, tpe1, tpe2), checkType(tc.setPos(b).withVCKind(VCKind.CheckType), b, BooleanType()) ++ tr1 ++ tr2)

      case Error(tpe, descr) =>
        val tr = isType(tc, tpe)
        (tpe, tr ++ buildVC(tc.withVCKind(VCKind.fromErr(Some(descr))).setPos(e), BooleanLiteral(false)))

      case Max(exprs) =>
        val (_, vcs) = exprs.foldLeft((tc, TyperResult.valid)){
          case ((tcAcc, tr), expr) =>
            (tcAcc.withTruth(expr), tr ++ checkType(tcAcc, expr, IntegerType()))
        }
        (IntegerType(), vcs)

      case And(exprs) =>
        val (_, vcs) = exprs.foldLeft((tc, TyperResult.valid)){
          case ((tcAcc, tr), expr) =>
            (tcAcc.withTruth(expr), tr ++ checkType(tcAcc, expr, BooleanType()))
        }
        (BooleanType(), vcs)

      case Or(exprs) =>
        val (_, vcs) = exprs.foldLeft((tc, TyperResult.valid)){
          case ((tcAcc, tr), expr) =>
            (tcAcc.withTruth(Not(expr)), tr ++ checkType(tcAcc, expr, BooleanType()))
        }
        (BooleanType(), vcs)

      case Implies(e1, e2) =>
        (BooleanType(),
          checkType(tc, e1, BooleanType()) ++
          checkType(tc.withTruth(e1), e2, BooleanType()))

      case Not(e) => (BooleanType(), checkType(tc, e, BooleanType()))

      case v@Variable(id, tpe, _) =>
        // TODO: Replace by constant time lookup?
        tc.termVariables.find(tv => tv.id == id) match {
          case Some(tv) => (tv.tpe, TyperResult.valid)
          case None =>
            reporter.fatalError(v.getPos, s"Variable ${id.asString} ${id.id} is not defined in context:\n${tc.asString()}")
        }

      case Equals(e1, e2) =>
        val (tpe1, tr1) = inferType(tc, e1)
        val (tpe2, tr2) = inferType(tc, e2)
        if (tpe1.getType != tpe2.getType) {
          reporter.fatalError(e.getPos, s"Comparing elements of different types:\n${e1.asString} of type ${tpe1.asString} and\n${e2.asString} of type ${tpe2.asString}")
        }
        (BooleanType(), tr1 ++ tr2)

      case Lambda(params, body) =>
        val trParams = areDependentTypes(tc, params)
        val (tpe, trBody) = inferType(tc.bind(params), body)
        if (params.isEmpty) (FunctionType(Seq(), tpe), trParams ++ trBody)
        else (PiType(params, tpe), trParams ++ trBody)

      case Application(e, es) =>
        val (tpe, tr) = inferType(tc, e)
        stripRefinementsAndAnnotations(tpe) match {
          case FunctionType(from, to) => (to, tr ++ checkTypes(tc, es, from))
          case PiType(from, to) => (insertFreshLets(from, es, to), tr ++ checkDependentTypes(tc, es, from))
        }

      case Let(vd, value, body) =>
        val trValue = checkType(tc.setPos(value).withVCKind(VCKind.CheckType), value, vd.tpe)
        val (tc2, id2) = tc.freshBindWithValue(vd, value)
        val freshBody: Expr = Substituter(immutable.Map(vd.id -> id2)).transform(body)
        val (tpe, trBody) = inferType(tc2.withLastPos(body), freshBody)
        (insertFreshLets(Seq(vd), Seq(value), tpe), trValue ++ trBody)

      case Assume(cond, body) =>
        val tr = checkType(tc.setPos(cond), cond, BooleanType())
        val (tpe, tr2) = inferType(tc.withTruth(cond), body)
        (tpe, tr ++ tr2)

      case Assert(cond, optErr, body) =>
        val kind = VCKind.fromErr(optErr)
        val tr = checkType(tc.withVCKind(kind).setPos(cond), cond, TrueBoolean())
        val (tpe, tr2) = inferType(tc.withTruth(cond), body)
        (tpe, tr ++ tr2)

      // NOTE: `require` clauses in functions are type-checked in `checkType(FunDef)`, but since
      // they can also appear in lambdas bodies, they need to be handled here as well.
      case Require(cond, body) =>
        val tr = checkType(tc.setPos(cond), cond, BooleanType())
        val (tpe, tr2) = inferType(tc.withTruth(cond), body)
        (tpe, tr ++ tr2)

      case FunctionInvocation(id, tps, args) =>
        val calleeFd = getFunction(id)
        val calleeTfd = calleeFd.typed(tps)

        checkFunctionIsVisible(tc, id, e)

        val fiS = shortString(e.asString, 40)

        import exprOps._

        val (tc2, freshener2) = tc.freshBindWithValues(calleeTfd.params, args)
        val specced = BodyWithSpecs(freshener2.transform(freshenLocals(calleeTfd.fullBody)))
        val n = specced.specs.count(_.kind == PreconditionKind)
        val trPre = specced.letsAndSpecs(PreconditionKind).foldLeft(
          (tc2, TyperResult.valid, 1)
        ) {
          case ((tcAcc, trAcc, i), LetInSpec(vd0, e0)) => (tcAcc.bindWithValue(vd0, e0), trAcc, i)
          case ((tcAcc, trAcc, i), Precondition(cond)) =>
            val kind = if (n == 1)
              VCKind.Info(VCKind.Precondition, s"call $fiS")
            else
              VCKind.Info(VCKind.Precondition, s"call $fiS (require $i/$n)")
            (
              tcAcc.withTruth(cond),
              trAcc ++ buildVC(tcAcc.withVCKind(kind).setPos(e), cond),
              i + 1
            )
          case _ => sys.error("not possible due to filtering")
        }._2

        val isRecursive = tc.currentFid.exists(fid => dependencies(id).contains(fid))

        val calleeMeasureOpt = measureOf(calleeTfd.fullBody).map(freshenLocals(_))
        val hasMeasure = calleeMeasureOpt.isDefined

        val trSize = {
          if (checkMeasures.isTrue && isRecursive && hasMeasure) {
            assert(tc.measureType.isDefined)
            assert(tc.currentMeasure.isDefined)
            val currentMeasure = tc.currentMeasure.get
            assert(calleeMeasureOpt.isDefined, s"${calleeTfd.id.asString} must have a measure")
            val calleeMeasure = calleeMeasureOpt.get
            val calleeMeasureValue = freshLets(calleeTfd.params, args, calleeMeasure)
            buildVC(
              tc.withVCKind(VCKind.MeasureDecreases).setPos(e),
              lessThan(tc.measureType.get, calleeMeasureValue, currentMeasure)
            )
          } else {
            TyperResult.valid
          }
        }

        val argsKind = VCKind.Error(s"argument types (call $fiS)")
        (insertFreshLets(calleeTfd.params, args, calleeTfd.returnType),
          checkDependentTypes(tc.withVCKind(argsKind), args, calleeTfd.params) ++
          trPre ++
          trSize)

      case ADTSelector(expr, selector) =>
        val (tpe, tr) = inferType(tc, expr)
        stripRefinementsAndAnnotations(tpe) match {
          // TODO: Check that this ADT is strictly positive
          case ADTType(id, tps) if tc.visibleADTs(id) =>
            val selectorType =
              lookupSort(id)
                .filter(_.tparams.size == tps.size)
                .map(_.typed(tps)).toSeq
                .flatMap(_.constructors.flatMap(_.fields))
                .find(_.id == selector).map(_.tpe).getOrElse(
                  reporter.fatalError(e.getPos, s"Unexpected type ${tpe.asString} for selector ${selector.asString}")
                )
            (selectorType, tr)
          case RecursiveType(id, tps, e) if tc.visibleADTs(id) =>
            val selectorType =
              lookupSort(id)
                .filter(_.tparams.size == tps.size)
                .map(_.typed(tps)).toSeq
                .flatMap(_.constructors.flatMap(_.fields))
                .find(_.id == selector).map(sel => sel.tpe).getOrElse(
                  reporter.fatalError(e.getPos, s"Unexpected type ${tpe.asString} for selector ${selector.asString}")
                )
            if (selectorType == baseType(id, selectorType)) {
              // In that case we do not need a strictly positive VC check for the index:
              (selectorType, tr)
            } else {
              (index(id, selectorType, Minus(e,IntegerLiteral(1))), tr ++ buildVC(tc.withVCKind(VCKind.UnfoldType), GreaterThan(e, IntegerLiteral(0))))
            }
          case _ =>
            reporter.fatalError(e.getPos, s"Type of ${expr.asString} is ${tpe.asString}, but an ADT was expected")
        }

      case SizedADT(id, tps, args, size) =>
        val cons = lookupConstructor(id).get
        val sortId = cons.sort
        val sort = getSort(sortId)
        val lookedUpConstructor =
          lookupSort(sortId)
            .filter(_.tparams.size == tps.size)
            .flatMap { sort =>
              sort.typed(tps).constructors
                .find(_.id == id)
                .filter(_.fields.size == args.size)
            }
        val trInv =
          if (sort.hasInvariant) {
            val inv = sort.typed(tps).invariant.get
            val invKind = VCKind.AdtInvariant(id)
            val tc2 = tc.withVCKind(invKind).setPos(e)
            if (inv.flags.contains(InlineInvariant)) {
              val (tc3, freshener) = tc2.freshBindWithValues(inv.params, Seq(e))
              buildVC(tc3, freshener.transform(inv.fullBody))
            } else {
              val application: Expr = inv.applied(Seq(e))
              buildVC(tc2, application)
            }
          } else
            TyperResult.valid

        val trZero = lookedUpConstructor.map { tcons =>
            checkDependentTypes(tc.withTruth(Equals(size, IntegerLiteral(0))),
            args,
            tcons.fields.map(vd => baseType(sortId, vd)))
        }.getOrElse (
          reporter.fatalError(e.getPos, s"Could not infer type for ${e.asString}")
        )

        val trSucc = lookedUpConstructor.map { tcons =>
            checkDependentTypes(tc.withTruth(GreaterThan(size, IntegerLiteral(0))),
            args,
            tcons.fields.map(vd => index(sortId, vd, pred(size))))
        }.getOrElse (
          reporter.fatalError(e.getPos, s"Could not infer type for ${e.asString}")
        )
        val kind = VCKind.fromErr(Some("Non-Negative Size for Sized ADT"))
        (RecursiveType(sortId, tps, size),
          trInv ++ trZero ++ trSucc ++ buildVC(tc.withVCKind(kind), GreaterEquals(size, IntegerLiteral(0))))

      case ADT(id, tps, args) =>
        val cons = getConstructor(id)
        val sortId = cons.sort
        val sort = getSort(sortId)

        val trInv =
          if (sort.hasInvariant) {
            val inv = sort.typed(tps).invariant.get
            val invKind = VCKind.AdtInvariant(inv.id)
            val tc2 = tc.withVCKind(invKind).setPos(e)
            if (inv.flags.contains(InlineInvariant)) {
              val (tc3, freshener) = tc2.freshBindWithValues(inv.params, Seq(e))
              buildVC(tc3, freshener.transform(inv.fullBody))
            } else {
              buildVC(tc2, inv.applied(Seq(e)))
            }
          } else {
            TyperResult.valid
          }

        val tr =
          lookupSort(sortId)
            .filter(_.tparams.size == tps.size)
            .flatMap { sort =>
              sort.typed(tps).constructors
                .find(_.id == id)
                .filter(_.fields.size == args.size)
                .map(tcons => checkDependentTypes(tc, args, tcons.fields))
            }.getOrElse(
              reporter.fatalError(e.getPos, s"Could not infer type for ${e.asString}")
            )

        (ADTType(sortId, tps), trInv ++ tr)

      case IsConstructor(expr, id) =>
        val (tpe, tr) = inferType(tc, expr)
        stripRefinementsAndAnnotations(tpe) match {
          case ADTType(sort, _) if (tc.visibleADTs(sort)) =>
            (lookupSort(sort), lookupConstructor(id)) match {
              case (Some(sort), Some(cons)) if sort.id == cons.sort =>
                (BooleanType(), tr)
              case _ =>
                reporter.fatalError(e.getPos, s"Type of ${expr.asString} is ${tpe.asString}, which does not have ${id.asString} as a constructor")
            }
          case RecursiveType(sort, _, _) if (tc.visibleADTs(sort)) =>
            (lookupSort(sort), lookupConstructor(id)) match {
              case (Some(sort), Some(cons)) if sort.id == cons.sort =>
                (BooleanType(), tr)
              case _ =>
                reporter.fatalError(e.getPos, s"Type of ${expr.asString} is ${tpe.asString}, which does not have ${id.asString} as a constructor")
            }
          case _ =>
            reporter.fatalError(e.getPos, s"The type of ${expr.asString} (${tpe.asString}) is not an ADT")
        }

      // @romac - FIXME: Properly typecheck Passes
      case p: Passes =>
        (BooleanType(), checkType(tc, p.asConstraint, BooleanType()))

      // @romac - FIXME: What should the result type actually be?
      case Forall(vds, pred) =>
        (BooleanType(), checkType(tc.bind(vds).setPos(pred), pred, BooleanType()))

      case c: Choose =>
        reporter.fatalError(c.getPos, s"The type-checker shouldn't encounter `choose`, as these are hidden under functions by the `ChooseEncoder` phase.")

      case _ =>
        reporter.fatalError(e.getPos, s"The type-checker doesn't support expressions: ${e.getClass}")
    }

    reporter.debug(s"\n${tc0.indent}Inferred type: ${t.asString} for ${e.asString}")

    (t, tr.root(InferType(tc0, e, t)))
  }

  def vcFromContext(l: Seq[Variable], e: Expr): Expr = l.map(v => v -> v.tpe) match {
    case Seq() => e
    case (x1, _) +: (_, LetEquality(x2: Variable, e2)) +: _ if x1.id == x2.id =>
      Let(x2.toVal, e2, vcFromContext(l.tail.tail, e))
    case (_, LetEquality(e1: Variable, e2)) +: _ =>
      Let(e1.toVal, e2, vcFromContext(l.tail, e))
    case (_, Truth(t)) +: _ =>
      Implies(t, vcFromContext(l.tail, e))
    case (x, RefinementType(vd, pred)) +: _ =>
      Implies(substVar(pred, vd.id, x), vcFromContext(l.tail, e))
    case _ =>
      vcFromContext(l.tail, e)
  }

  def isPathCondition(v: Variable): Boolean = {
    v.tpe match {
      case LetEquality(_, _) => true
      case Truth(_) => true
      case RefinementType(_, _) => true
      case _ => false
    }
  }

  def buildVC(tc: TypingContext, e: Expr): TyperResult = {
    require(tc.currentFid.isDefined)

    def splitAndFilterUnchecked(e: Expr): Seq[Expr] = e match {
      case Let(vd, expr, body) => splitAndFilterUnchecked(body).map(Let(vd, expr, _).setPos(e))
      case And(exprs) =>
        val filteredExprs = exprs.flatMap(splitAndFilterUnchecked)
        if (filteredExprs.isEmpty) Seq()
        else if (filteredExprs.size == 1) Seq(filteredExprs.head)
        else Seq(And(filteredExprs).setPos(e))
      case Annotated(_, flags) if flags.contains(DropConjunct) => Seq()
      case SplitAnd(exprs) => exprs.flatMap(splitAndFilterUnchecked)
      case Annotated(body, flags) => splitAndFilterUnchecked(body).map(Annotated(_, flags).setPos(e))
      case _ => Seq(e)
    }

    val exprs = splitAndFilterUnchecked(e)

    if (exprs.isEmpty) {
      return TyperResult.valid
    }

    val conditions = exprs.map(vcFromContext(tc.termVariables, _))

    val vcs: Seq[StainlessVC] = conditions.map(condition => StainlessVC(
      condition,
      tc.currentFid.get,
      tc.vcKind,
      tc.checkSAT,
    ).setPos(tc)).filter(vcFilter.withEmitVCs(tc.emitVCs))

    if (vcs.isEmpty) {
      return TyperResult.valid
    }

    reporter.debug(
      s"Created VCs in context:\n${tc.asString()}\nfor expression: ${e.asString}\n\n" +
      s"VCs:\n${conditions.map(_.asString).mkString("\n")}\n\n\n"
    )(using DebugSectionTypeCheckerVCs)

    TyperResult(vcs, exprs.map(expr => NodeTree(JVC(tc, expr): Judgment, Seq())))
  }

  /** The `checkType` function checks that an expression `e` has type `tpe` by
    * generating a sequence of verification conditions to be checked. If `e`
    * does not have type `tpe`, the function emits a `TypeCheckingException`.
    */
  def checkType(tc0: TypingContext, e: Expr, tpe: Type): TyperResult = {
    reporter.debug(s"\n${tc0.indent}Checking that: ${e.asString} (${e.getPos})")
    reporter.debug(s"${tc0.indent}has type: ${tpe.asString}")
    reporter.debug(s"${tc0.indent}in context")
    reporter.debug(tc0.asString(tc0.indent))

    val tc = tc0.inc()
    val res = (e, tpe) match {

      // High-priority rules for `Top`.
      // Unapply for `Top` matches any `ValueType(_)`
      case (v@Variable(id, _, _), Top()) =>
        if (tc.termVariables.exists(tv => tv.id == v.id)) TyperResult.valid
        else reporter.fatalError(v.getPos,
          s"Variable ${id.asString} is not defined in context:\n${tc.asString()}")

      case (UnitLiteral(), Top()) => TyperResult.valid
      case (BooleanLiteral(_), Top()) => TyperResult.valid
      case (IntegerLiteral(_), Top()) => TyperResult.valid
      case (StringLiteral(_), Top()) => TyperResult.valid
      case (FractionLiteral(_, _), Top()) => TyperResult.valid
      case (BVLiteral(_, _, _), Top()) => TyperResult.valid

      case (FiniteSet(elements, tpe), Top()) => checkTypes(tc, elements, Top())
      case (FiniteBag(pairs, tpe), Top()) =>
        checkTypes(tc, pairs.map(_._1), Top()) ++
        checkTypes(tc, pairs.map(_._2), Top())
      case (FiniteMap(pairs, default, _, _), Top()) =>
        checkTypes(tc, pairs.map(_._1), Top()) ++
        checkTypes(tc, pairs.map(_._2), Top()) ++
        checkType(tc, default, Top())
      case (FiniteArray(elements, tpe), Top()) => checkTypes(tc, elements, Top())
      case (Tuple(elements), Top()) => checkTypes(tc, elements, Top())
      case (Lambda(_, _), Top()) => TyperResult.valid // TODO: Perhaps check that the free variables of `e` are in the context?
      case (SizedADT(id, tps, args, size), Top()) => checkTypes(tc, args, Top()) ++ checkType(tc, size, Top())
      case (ADT(id, tps, args), Top()) => checkTypes(tc, args, Top())
      case (_, Top()) => inferType(tc, e)._2 // We ignore the inferred type but keep the VCs

      case (Tuple(es), TupleType(tps)) =>
        checkTypes(tc, es, tps)

      case (Tuple(es), SigmaType(from, to)) =>
        checkDependentTypes(tc, es.init, from) ++
        checkType(tc.bindWithValues(from, es.init), es.last, to)

      case (Lambda(params1, body), FunctionType(params2, to)) =>
        val (vds, retyped) = params1.zip(params2).foldLeft((Seq.empty[ValDef], Map.empty[Variable, Type])) {
          case ((accVds, accRetyped), (vd, tp)) =>
            if (vd.tpe == tp) (accVds :+ vd, accRetyped)
            else (accVds :+ vd.copy(tpe = tp), accRetyped + (vd.toVariable -> tp)) // May happen for refined types
        }
        val body2 = retypeVariables(retyped, body)
        checkType(tc.bind(vds), body2, to)

      case (Lambda(params1, body), PiType(params2, to)) =>
        val freshener = Substituter(params1.map(_.id).zip(params2.map(_.id)).toMap)
        checkType(tc.bind(params2), freshener.transform(body), to)

      case (Let(vd, value, body), _) =>
        val (tc2, id2) = tc.freshBindWithValue(vd, value)
        val freshBody: Expr = Substituter(immutable.Map(vd.id -> id2)).transform(body)
        checkType(tc.setPos(value).withVCKind(VCKind.CheckType), value, vd.tpe) ++
        checkType(tc2.withLastPos(body), freshBody, tpe)

      case (Assert(cond, optErr, body), _) =>
        val kind = VCKind.fromErr(optErr)
        checkType(tc, cond, BooleanType()) ++
        buildVC(tc.withVCKind(kind).setPos(cond), cond) ++
        checkType(tc.withTruth(cond), body, tpe)

      case (m: MatchExpr, _) => checkType(tc, matchToIfThenElse(e, false), tpe)

      case (IfExpr(b, e1, e2), _) =>
        checkType(tc.setPos(b).withVCKind(VCKind.CheckType), b, BooleanType()) ++
        checkType(tc.withTruth(b).withLastPos(e1), e1, tpe) ++
        checkType(tc.withTruth(Not(b)).withLastPos(e2), e2, tpe)

      case (e, TrueBoolean()) =>
        checkType(tc.withVCKind(VCKind.CheckType), e, BooleanType()) ++ buildVC(tc, e)

      case (e, RefinementType(vd, prop)) =>
        val (tc2, freshener) = tc.freshBindWithValues(Seq(vd), Seq(e))
        checkType(tc.withVCKind(VCKind.CheckType), e, vd.tpe) ++ checkType(tc2, freshener.transform(prop), TrueBoolean())

      case (UncheckedExpr(e), tpe) =>
        val (inferredType, tr) = inferType(tc.withEmitVCs(false), e)
        tr ++ isSubtype(tc, inferredType, tpe)

      case (Annotated(e, _), _) => checkType(tc, e, tpe)
      case (_, AnnotatedType(tpe, flags)) => checkType(tc, e, tpe)

      case _ =>
        val (inferredType, tr) = inferType(tc, e)
        tr ++ isSubtype(tc, inferredType, tpe)
    }
    reporter.debug(s"\n${tc0.indent}Checked that: ${e.asString} (${e.getPos})")
    reporter.debug(s"${tc0.indent}has type: ${tpe.asString}")
    reporter.debug(s"${tc0.indent}in context:")
    reporter.debug(s"${tc0.asString(tc0.indent)}")
    res.root(CheckType(tc0, e, tpe))
  }

  def isSubtype(tc0: TypingContext, _tp1: Type, _tp2: Type): TyperResult = {
    val tp1 = exprOps.stripAnnotations(_tp1)
    val tp2 = exprOps.stripAnnotations(_tp2)
    reporter.debug(s"\n${tc0.indent}Checking that: ${tp1.asString}")
    reporter.debug(s"${tc0.indent}is a subtype of: ${tp2.asString}")
    reporter.debug(s"${tc0.indent}in context:")
    reporter.debug(tc0.asString(tc0.indent))
    val tc = tc0.inc()
    val res = if (tp1 == tp2) TyperResult.valid
    else (tp1, tp2) match {
      case (_, Top()) => TyperResult.valid

      case (TupleType(tps1), TupleType(tps2)) if tps1.size == tps2.size =>
        areSubtypes(tc, tps1, tps2)

      case (TupleType(tps1), SigmaType(params2, to2)) if tps1.size == params2.size + 1 =>
        val params1 = tps1.zip(params2).map { case (tp, vd) => ValDef.fresh(vd.id.name, tp) }
        val (tc2, freshener, tr) = areSubtypes(tc, params1, params2)
        tr ++ isSubtype(tc2, tps1.last, freshener.transform(to2))

      case (SigmaType(params1, to1), TupleType(tps2)) if tps2.size == params1.size + 1 =>
        val params2 = tps2.zip(params1).map { case (tp, vd) => ValDef.fresh(vd.id.name, tp) }
        val (tc2, freshener, tr) = areSubtypes(tc, params1, params2)
        tr ++ isSubtype(tc2, freshener.transform(to1), tps2.last)

      case (SigmaType(params1, to1), SigmaType(params2, to2)) =>
        val (tc2, freshener, tr) = areSubtypes(tc, params1, params2)
        tr ++ isSubtype(tc2, freshener.transform(to1), freshener.transform(to2))

      case (RefinementType(vd1, prop1), RefinementType(vd2, prop2)) if (vd1.tpe == vd2.tpe) =>
        buildVC(
          tc.bind(vd1).withTruth(prop1).withVCKind(VCKind.RefinementSubtype),
          substVar(prop2, vd2.id, vd1.toVariable)
        )

      case (_, RefinementType(vd, prop)) =>
        isSubtype(tc, tp1, vd.tpe) ++ buildVC(tc.withVCKind(VCKind.RefinementSubtype), prop)

      case (RefinementType(vd, prop), _) =>
        isSubtype(tc, vd.tpe, tp2)

      case (FunctionType(from1, to1), FunctionType(from2, to2)) =>
        areSubtypes(tc, from2, from1) ++ isSubtype(tc, to1, to2)

      case (PiType(params1, to1), FunctionType(from2, to2)) =>
        val params2 = from2.zip(params1).map { case (tp, vd) => ValDef.fresh(vd.id.name, tp) }
        val (tc2, freshener, tr) = areSubtypes(tc, params2, params1)
        tr ++ isSubtype(tc2, freshener.transform(to1), to2)

      case (FunctionType(from1, to1), PiType(params2, to2)) =>
        val params1 = from1.zip(params2).map { case (tp, vd) => ValDef.fresh(vd.id.name, tp) }
        val (tc2, freshener, tr) = areSubtypes(tc, params2, params1)
        tr ++ isSubtype(tc2, freshener.transform(to1), to2)

      case (PiType(params1, to1), PiType(params2, to2)) =>
        val (tc2, freshener, tr) = areSubtypes(tc, params2, params1)
        tr ++ isSubtype(tc2, freshener.transform(to1), freshener.transform(to2))

      case (ADTType(id1, tps1), RecursiveType(id2, tps2, index2))
          if id1 == id2 && tps1.length == tps2.length =>
        TyperResult(tps1.zip(tps2).map { case (tp1, tp2) => areEqualTypes(tc, tp1, tp2) })

      case (ADTType(id1, tps1), ADTType(id2, tps2))
          if id1 == id2 && tps1.length == tps2.length =>
        TyperResult(tps1.zip(tps2).map { case (tp1, tp2) => areEqualTypes(tc, tp1, tp2) })

      // The equality VC can be relaxed to >= for positive types
      case (RecursiveType(id1, tps1, index1), RecursiveType(id2, tps2, index2))
          if id1 == id2 && tps1.length == tps2.length =>
        TyperResult(tps1.zip(tps2).map { case (tp1, tp2) => areEqualTypes(tc, tp1, tp2) }) ++
        buildVC(tc.withVCKind(VCKind.RecursiveSubtype), Equals(index1, index2))

      case (SetType(base1), SetType(base2)) =>
        areEqualTypes(tc, base1, base2)

      case (BagType(base1), BagType(base2)) =>
        areEqualTypes(tc, base1, base2)

      case (MapType(from1, to1), MapType(from2, to2)) =>
        areEqualTypes(tc, from1, from2) ++
        areEqualTypes(tc, to1, to2)

      case (ArrayType(base1), ArrayType(base2)) =>
        areEqualTypes(tc, base1, base2)

      case (_, _) =>
        reporter.fatalError(tc.getPos, s"Could not check that ${tp1.asString} is a subtype of ${tp2.asString}")
    }
    reporter.debug(s"\n${tc0.indent}Checked that: ${tp1.asString} (${tp1.getPos})")
    reporter.debug(s"${tc0.indent}is a subtype of: ${tp2.asString}")
    reporter.debug(s"${tc0.indent}in context:")
    reporter.debug(s"${tc0.asString(tc0.indent)}")
    res.root(IsSubtype(tc0, tp1, tp2))
  }

  /** The `areEqualTypes` checks the subtyping relation in both directions */
  def areEqualTypes(tc0: TypingContext, t1: Type, t2: Type): TyperResult = {
    reporter.debug(s"\n${tc0.indent}Checking that: ${t1.asString} and ${t2.asString} are equal types")
    reporter.debug(s"${tc0.indent}in context:")
    reporter.debug(tc0.asString(tc0.indent))

    val tc = tc0.inc()
    val tr = if (t1 == t2) TyperResult.valid else {
      isSubtype(tc, t1, t2) ++ isSubtype(tc, t2, t1)
    }

    tr.root(AreEqualTypes(tc0, t1, t2))
  }

  def checkFunctionIsVisible(tc: TypingContext, id: Identifier, in: Expr): Unit = {
    if (tc.visibleFunctions(id)) return

    val errorInfo = tc.currentFid flatMap { currentFid =>
      val currentDeps = dependencies(currentFid)
      val mutuallyRecursiveDeps = currentDeps.filter { did =>
        dependencies(did).contains(currentFid)
      }

      if (mutuallyRecursiveDeps.contains(id)) {
        Some(s", because it is mutually recursive with the current function ${currentFid.asString}")
      } else {
        None
      }
    }

    reporter.fatalError(in.getPos,
      s"Call to function ${id.asString} is not allowed here${errorInfo.getOrElse("")}"
    )
  }

  def needsMeasure(fd: FunDef): Boolean = {
    checkMeasures.isTrue &&
    symbols.isRecursive(fd.id) &&
    !fd.flags.contains(Synthetic) &&
    !fd.flags.exists(_.name == "library")
  }

  def checkType(id: Identifier): (Option[Type], TyperResult) = {
    import exprOps._

    val fd = getFunction(id)
    val deps = dependencies(id)
    val mutuallyRecursiveDeps = deps.filter { id2 => dependencies(id2).contains(id) }

    // NOTE: We currently trust that synthetic functions with mutual
    // recursion with an ADT are sound (eg. those generated by TypeEncoding).
    if (!fd.flags.contains(Synthetic)) {
      mutuallyRecursiveDeps
        .find(sort => lookupSort(sort).isDefined)
        .foreach { sort =>
          reporter.fatalError(fd.getPos,
            s"An ADT (${sort.asString}), and a function (${id.asString}) cannot be mutually recursive")
        }
    }

    val toFreshen = fd.tparams.map(tpd => tpd.tp.id) ++ fd.params.map(vd => vd.id)

    val freshener = Substituter(toFreshen.map(id => id -> id.freshen).toMap)

    val specced = BodyWithSpecs(fd.fullBody)

    // The type of the arguments, the specifications, and the return type
    // need to be well-formed without the mutually recursive dependencies
    val nonMutuallyRecursiveContext: TypingContext =
      TypingContext.empty.
        withIdentifiers(deps -- mutuallyRecursiveDeps).
        withTypeVariables(fd.tparams.map(tpd => freshener.transformTp(tpd.tp)).toSet).
        inFunction(id).
        setPos(fd)

    // `tc0` is `nonMutuallyRecursiveContext` to which we add variables for the
    // arguments of the function
    // `trArgs` are the verification conditions for ensuring that the type of
    // the arguments are well-formed
    val (tc0, trArgs): (TypingContext, TyperResult) = fd.params.foldLeft(nonMutuallyRecursiveContext, TyperResult.valid) {
      case ((tcAcc, trAcc), vd) =>
        val freshVd: ValDef = freshener.transform(vd)
        (
          tcAcc.bind(freshVd),
          trAcc ++ isType(tcAcc, freshVd.tpe)
        )
    }

    // `tcWithPre` is `tc0` to which we add the preconditions and lets
    // and `trPre` is the `TyperResult` corresponding to type-checking those
    val (tcWithPre, trPre): (TypingContext, TyperResult) = specced.specs.filter(spec => spec.kind == LetKind || spec.kind == PreconditionKind).foldLeft (tc0, TyperResult.valid) {
      case ((tcAcc, trAcc), LetInSpec(vd, e)) =>
        val e2 = freshener.transform(e)
        val freshVd = freshener.transform(vd)
        (tcAcc.bindWithValue(freshVd, e2), trAcc ++ checkType(tcAcc, e2, freshVd.tpe))
      case ((tcAcc, trAcc), Precondition(cond)) =>
        val cond2 = freshener.transform(cond)
        (tcAcc.withTruth(cond2), trAcc ++ checkType(tcAcc, cond2, BooleanType()))
      case _ => sys.error("shouldn't be possible because of the filtering above")
    }

    // We check that the specification is SAT to avoid false => P(body(x)) type of proofs
    // To do so, we create a VC phi(x) => false, where phi(x) is the precondition. This will be checked as phi(x) => not false
    // Then we check in VerificationChecker that this VC should be SAT
    val trPreSat: Option[TyperResult] = if checkSatPrecond then Some(buildVC(tcWithPre.withCheckSAT(false).withVCKind(VCKind.SATPrecondCheck), BooleanLiteral(false))) else None

    val measureOpt = specced.getSpec(MeasureKind).map(measure => freshener.transform(measure.expr))

    val (measureType, trMeasure): (Option[Type], TyperResult) =
      if (measureOpt.isDefined) {
        val measure = measureOpt.get
        val (measureType, trMeasureType) = inferType(tcWithPre, measure)
        val trMeasurePos = buildVC(
          tcWithPre.withVCKind(VCKind.MeasurePositive).setPos(measure),
          positive(measureType, measure)
        )

        (Some(measureType), trMeasureType ++ trMeasurePos)
      } else {
        (None, TyperResult.valid)
      }

    val postOpt = specced.getSpec(PostconditionKind).map(post => freshener.transform(post.expr))

    val freshenedReturnType: Type = freshener.transform(fd.returnType)
    val bodyOpt = specced.bodyOpt.map(freshener.transform)

    // The `TypingContext` for the body contains all dependencies, and the measure
    val tcBody = tcWithPre.withIdentifiers(deps).withMeasureType(measureType).withMeasure(measureOpt)

    // We check that the body of the function respects the return type and
    // the post-condition. We allow here references to mutually recursive dependencies (in `deps`)
    val trBody = bodyOpt.fold(TyperResult.valid) { body =>
      postOpt.fold(checkType(tcBody, body, freshenedReturnType)) {
        case Lambda(Seq(retArg), postBody) =>
          val refinedReturnType: RefinementType = RefinementType(retArg, postBody)
          val vcKind = if (fd.flags.contains(Law)) VCKind.Law else VCKind.Postcondition

          checkType(tcBody.withVCKind(vcKind), body, refinedReturnType)
        }
    }

    (measureType, (trArgs ++ trPre ++ trPreSat.getOrElse(TyperResult.valid) ++ trMeasure ++ trBody).root(OKFunction(id)))
  }

  def checkType(fids: Seq[Identifier]): Seq[StainlessVC] = {
    val checkedFunctions = fids.map(fid => fid -> checkType(fid))

    val vcs = (for ((id, (measureType, tr)) <- checkedFunctions) yield {
      val fd = getFunction(id)

      if (exprOps.BodyWithSpecs(fd.fullBody).bodyOpt.isDefined) {
        val nm = needsMeasure(fd)
        if (nm && measureType.isEmpty) {
          Seq(StainlessVC(BooleanLiteral(false), id, VCKind.MeasureMissing, false).setPos(fd))
        } else {
          if (nm) {
            checkedFunctions.find { case (id2, (measureType2, _)) =>
              dependencies(id).contains(id2) &&
              dependencies(id2).contains(id) &&
              measureType2.map(_.getType) != measureType.map(_.getType) // type without refinements
            } match {
              case None => ()
              case Some((id2, (None, _))) =>
                reporter.fatalError(fd.getPos,
                  s"Measure of ${id.asString} has type ${measureType.get} while mutually recursive function " +
                  s"${id2.asString} has no measure")
              case Some((id2, (Some(measureType2), _))) =>
                reporter.fatalError(fd.getPos,
                  s"Measure of ${id.asString} has type ${measureType.get} while mutually recursive function " +
                  s"${id2.asString} has measure with type ${measureType2}")
            }
          }
          val TyperResult(vcs, trees) = tr

          if (reporter.debugSections.contains(DebugSectionDerivation)) {
            makeHTMLFile(id.uniqueName + ".html", trees)
          }

          vcs

        }
      } else {
        Nil
      }
    }).flatten
    vcs.sortBy { vc =>
      (
        getFunction(vc.fid),
        vc.kind.underlying match {
          case VCKind.Law          => 0
          case VCKind.Precondition => 1
          case VCKind.Assert       => 2
          case _                   => 3
        }
      )
    }
  }

  // NOTE: We currently trust that synthetic sorts with mutual
  // recursion with a function are sound (eg. those generated by TypeEncoding).
  def checkADTRefinementRecursion(sort: ADTSort): Unit =
    if (!sort.flags.contains(Synthetic)) {
      val deps = dependencies(sort.id)

      deps.find(fid => lookupFunction(fid).isDefined && dependencies(fid).contains(sort.id)) match {
        case Some(fid) =>
          reporter.fatalError(sort.getPos, s"An ADT (${sort.id.asString}), and a function (${fid.asString}) cannot be mutually recursive")
        case None => ()
      }
    }

  def wellFormedADT(sort: ADTSort): Seq[StainlessVC] = {
    checkADTRefinementRecursion(sort)

    val id = sort.id
    val deps = dependencies(id)

    val tc = TypingContext.empty.
      withIdentifiers(deps).
      withTypeVariables(sort.tparams.map(_.tp).toSet).
      inADT(id).
      setPos(sort)

    val TyperResult(vcs, trees) = TyperResult(
      sort.constructors.map(cons =>
        areDependentTypes(tc, cons.fields)
      )
    ).root(OKADT(id))

    if (reporter.debugSections.contains(DebugSectionDerivation)) {
      makeHTMLFile(id.uniqueName + ".html", trees)
    }

    vcs
  }

  def wellFormedADTs(): Seq[StainlessVC] = {
    sorts.toSeq.flatMap { case (_, sort) => wellFormedADT(sort) }
  }

  def checkFunctionsAndADTs(funs: Seq[Identifier]): Seq[StainlessVC] = {
    wellFormedADTs() ++ checkType(funs)
  }
}

object TypeChecker {
  def apply(p: StainlessProgram, ctx: inox.Context): TypeChecker { val program: p.type } = {
    class Impl(override val program: p.type) extends TypeChecker(p, ctx, VCFilter.fromOptions(ctx.options))
    new Impl(p)
  }
}
