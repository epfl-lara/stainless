/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait EffectElaboration
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with RefTransform { self =>
  val s: Trees
  val t: s.type
  import s._

  // Function rewriting depends on the effects analysis which relies on all dependencies
  // of the function, so we use a dependency cache here.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult](
    (fd, context) => getDependencyKey(fd.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult](
    (sort, context) => getDependencyKey(sort.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult](
    (cd, context) => ClassKey(cd) + OptionSort.key(context.symbols)
  )

  override protected type FunctionResult = t.FunDef
  override protected def registerFunctions(symbols: t.Symbols,
      functions: Seq[t.FunDef]): t.Symbols =
    symbols.withFunctions(functions)

  override protected final type ClassResult = (t.ClassDef, Option[t.FunDef])
  override protected final def registerClasses(symbols: t.Symbols,
      classResults: Seq[ClassResult]): t.Symbols = {
    val (classes, unapplyFds) = classResults.unzip
    symbols.withClasses(classes).withFunctions(unapplyFds.flatten)
  }

  protected class TransformerContext(val symbols: Symbols) extends RefTransformContext

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  override protected def extractSymbols(tctx: TransformerContext, symbols: s.Symbols): t.Symbols = {
    // We filter out the definitions related to AnyHeapRef since they are only needed for infering which
    // types live in the heap
    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.filterNot(fd => hasFlag(fd, "refEq")).toSeq)
      .withClasses(symbols.classes.values.filterNot(cd => hasFlag(cd, "anyHeapRef")).toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    super.extractSymbols(tctx, newSymbols)
      .withSorts(Seq(refSort) ++ OptionSort.sorts(newSymbols))
      .withFunctions(OptionSort.functions(newSymbols))
  }

  override protected def extractFunction(tctx: TransformerContext, fd: FunDef): FunDef =
    tctx.refTransformer.transform(fd)

  override protected def extractSort(tctx: TransformerContext, sort: ADTSort): ADTSort =
    tctx.refTransformer.transform(sort)

  override protected def extractClass(tctx: TransformerContext, cd: ClassDef): ClassResult =
    (tctx.refTransformer.transform(cd), tctx.makeClassUnapply(cd))
}

object EffectElaboration {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new EffectElaboration {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}

/** The actual Ref transformation **/

trait RefTransform extends oo.CachingPhase with utils.SyntheticSorts { self =>
  val s: Trees
  val t: s.type

  import s._
  import dsl._

  /* Heap encoding */

  private[this] lazy val refId: Identifier = ast.SymbolIdentifier("stainless.lang.Ref")
  private[this] lazy val refValue: Identifier = FreshIdentifier("value")
  private[this] lazy val refCons: Identifier = ast.SymbolIdentifier("stainless.lang.RefC")
  protected lazy val refSort: ADTSort = mkSort(refId)() { _ =>
    Seq((refCons, Seq(ValDef(refValue, IntegerType()))))
  }
  private[this] lazy val RefType: Type = T(refId)()
  private[this] def Ref(value: Expr): Expr = E(refCons)(value)
  private[this] def getRefValue(ref: Expr): Expr = ref.getField(refValue)

  protected lazy val HeapType: MapType = MapType(RefType, AnyType())

  // A sentinel value for the global heaps
  private[this] lazy val TheHeap = NoTree(MutableMapType(HeapType.from, HeapType.to))

  private[this] lazy val unapplyId = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)

  /* The transformer */

  protected type TransformerContext <: RefTransformContext

  trait RefTransformContext { context: TransformerContext =>
    implicit val symbols: s.Symbols

    lazy val livesInHeap = new utils.ConcurrentCached[Type, Boolean](isHeapType(_))

    private def isHeapType(tpe: Type): Boolean = tpe match {
      case AnyHeapRef() => true
      case ct: ClassType => ct.tcd.ancestors.exists(a => livesInHeap(a.toType))
      case _ => false
    }

    def smartLet(vd: => ValDef, e: Expr)(f: Expr => Expr): Expr = e match {
      case _: Terminal => f(e)
      case _ => let(vd, e)(f)
    }

    def classTypeInHeap(ct: ClassType): ClassType =
      ClassType(ct.id, ct.tps.map(refTransformer.transform)).copiedFrom(ct)

    def valueFromHeap(recv: Expr, objTpe: ClassType, fromE: Expr): Expr = {
      val app = MutableMapApply(TheHeap, recv).copiedFrom(fromE)
      val aio = AsInstanceOf(app, objTpe).copiedFrom(fromE)
      val iio = IsInstanceOf(app, objTpe).copiedFrom(fromE)
      Assume(iio, aio).copiedFrom(fromE)
    }

    def makeClassUnapply(cd: ClassDef): Option[FunDef] = {
      if (!livesInHeap(cd.typed.toType))
        return None

      import OptionSort._
      Some(mkFunDef(unapplyId(cd.id), t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get))(
          cd.typeArgs.map(_.id.name) : _*) { tparams =>
        val tcd = cd.typed(tparams)
        val ct = tcd.toType
        val objTpe = classTypeInHeap(ct)

        (Seq("x" :: RefType), T(option)(objTpe), { case Seq(x) =>
          Reads(FiniteSet(Seq(x), RefType), Modifies(FiniteSet(Seq(), RefType),
            if_ (IsInstanceOf(MutableMapApply(TheHeap, x), objTpe)) {
              C(some)(objTpe)(AsInstanceOf(MutableMapApply(TheHeap, x), objTpe))
            } else_ {
              C(none)(objTpe)()
            }
          ))
        })
      })
    }

    // Reduce all mutation to MutableMap updates
    // TODO: Handle mutable types other than classes
    object refTransformer extends SelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        // Reference equality is transformed into value equality on references
        case RefEq(e1, e2) =>
          Equals(transform(e1), transform(e2))

        case ClassConstructor(ct, args) if livesInHeap(ct) =>
          // TODO: Add mechanism to keep multiple freshly allocated objects apart
          val ref = Choose("ref" :: RefType, BooleanLiteral(true)).copiedFrom(e)
          let("ref" :: RefType, ref) { ref =>
            val ctNew = ClassType(ct.id, ct.tps.map(transform)).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform)).copiedFrom(e)
            let("alloc" :: UnitType(), MutableMapUpdate(TheHeap, ref, value).copiedFrom(e)) { _ =>
              ref
            }
          }

        case ClassSelector(recv, field) if livesInHeap(recv.getType) =>
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: RefType, transform(recv)) { recvRef =>
            ClassSelector(valueFromHeap(recvRef, objTpe, e), field).copiedFrom(e)
          }

        case FieldAssignment(recv, field, value) =>
          assert(livesInHeap(recv.getType))
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: RefType, transform(recv)) { recvRef =>
            val oldObj = valueFromHeap(recvRef, objTpe, e)
            let("oldObj" :: objTpe, oldObj) { oldObj =>
              val newCt = objTpe.asInstanceOf[ClassType]
              val newArgs = newCt.tcd.fields.map {
                case vd if vd.id == field => transform(value)
                case vd => ClassSelector(oldObj, vd.id).copiedFrom(e)
              }
              val newObj = ClassConstructor(newCt, newArgs).copiedFrom(e)
              MutableMapUpdate(TheHeap, recvRef, newObj).copiedFrom(e)
            }
          }

        case IsInstanceOf(recv, tpe) if livesInHeap(tpe) =>
          val ct = tpe.asInstanceOf[ClassType]
          val app = MutableMapApply(TheHeap, transform(recv)).copiedFrom(e)
          IsInstanceOf(app, classTypeInHeap(ct)).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(pat: Pattern): Pattern = pat match {
        case ClassPattern(binder, ct, subPats) if livesInHeap(ct) =>
          val newClassPat = ClassPattern(
            None,
            classTypeInHeap(ct),
            subPats.map(transform)
          ).copiedFrom(pat)
          UnapplyPattern(
            binder.map(transform),
            Seq(),
            unapplyId(ct.id),
            ct.tps.map(transform),
            Seq(newClassPat)
          ).copiedFrom(pat)
        case _ =>
          super.transform(pat)
      }

      override def transform(tpe: Type): Type = tpe match {
        case ct: ClassType if livesInHeap(ct) =>
          RefType
        case FunctionType(_, _) =>
          val FunctionType(from, to) = super.transform(tpe)
          FunctionType(HeapType +: from, T(to, HeapType))
        // TODO: PiType
        case _ =>
          super.transform(tpe)
      }

      override def transform(cd: ClassDef): ClassDef = {
        val env = initEnv
        // FIXME: Transform type arguments in parents?

        // We remove the AnyHeapRef from the parents since it is just used for heap contracts type inference
        val newParents = cd.parents.filter {
          case AnyHeapRef() => false
          case _ => true
        }

        new ClassDef(
          transform(cd.id, env),
          cd.tparams.map(transform(_, env)),
          newParents,
          cd.fields.map(transform(_, env)),
          cd.flags.map(transform(_, env))
        ).copiedFrom(cd)
      }
    }
  }
}
