/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait StateInstrumentation extends oo.CachingPhase { self =>
  val s: Trees
  val t: s.type

  import s._
  import dsl._

  /* Heap encoding */

  private[this] lazy val refId: Identifier = FreshIdentifier("Ref")
  private[this] lazy val refValue: Identifier = FreshIdentifier("value")
  private[this] lazy val refCons: Identifier = FreshIdentifier("Ref")
  protected lazy val refSort: ADTSort = mkSort(refId)() { _ =>
    Seq((refCons, Seq(ValDef(refValue, IntegerType()))))
  }
  private[this] lazy val RefType: Type = T(refId)()
  private[this] def Ref(value: Expr): Expr = E(refCons)(value)
  private[this] def getRefValue(ref: Expr): Expr = ref.getField(refValue)

  protected lazy val HeapType: MapType = MapType(RefType, AnyType())

  // A sentinel value for the first transformation
  private[this] lazy val TheHeap = NoTree(HeapType)

  /* Instrumentation */

  protected type TransformerContext <: InstrumentationContext

  trait InstrumentationContext { context: TransformerContext =>
    implicit val symbols: s.Symbols

    def smartLet(vd: => ValDef, e: Expr)(f: Expr => Expr): Expr = e match {
      case _: Terminal => f(e)
      case _ => let(vd, e)(f)
    }

    def freshStateParam(): ValDef = "s0" :: HeapType

    // TODO: Perform some effect analysis to omit some state parameters
    def adjustFunSig(fd: FunDef): FunDef = {
      val fdStripped = fd.copy(fullBody = exprOps.withBody(fd.fullBody, NoTree(fd.returnType)))
      val fdWithRefs = refTransformer.transform(fdStripped)
      val (params, returnType) = if (isPureFunction(fd.id)) {
        (fdWithRefs.params, fdWithRefs.returnType)
      } else {
        val stateParam = freshStateParam().copiedFrom(fdWithRefs)
        (stateParam +: fdWithRefs.params, T(fdWithRefs.returnType, HeapType))
      }
      fdWithRefs.copy(params = params, returnType = returnType)
    }

    // Compute symbols with modified signatures and added sorts. Only used during instrumentation.
    val adjustedSymbols: s.Symbols = {
      val syms = context.symbols
      syms
        .withFunctions(syms.functions.values.map(adjustFunSig).toSeq)
        .withSorts(Seq(refSort) ++ syms.sorts.values.map(refTransformer.transform).toSeq)
        .withClasses(syms.classes.values.map(refTransformer.transform).toSeq)
    }

    def validHeapField(heap: Expr, key: Expr, tpe: Type): Expr =
      IsInstanceOf(MutableMapApply(heap, key), tpe)

    def erasesToRef(tpe: Type): Boolean = tpe match {
      case ct: ClassType => symbols.isMutableClassType(ct)
      case _ => false
    }

    // HACK: Introduce and use some purity analysis
    def isPureFunction(id: Identifier): Boolean =
      id.name == "size" && symbols.getFunction(id).flags.contains(Library) ||
      id.name == "isWithin"

    // Reduce all mutation to MutableMap updates
    // TODO: Handle mutable types other than classes
    object refTransformer extends SelfTreeTransformer {
      def classTypeInHeap(ct: ClassType): ClassType =
        ClassType(ct.id, ct.tps.map(transform)).copiedFrom(ct)

      override def transform(e: Expr): Expr = e match {
        case ClassConstructor(ct, args) if erasesToRef(ct) =>
          // TODO: Add mechanism to keep multiple freshly allocated objects apart
          val ref = Choose("ref" :: RefType, BooleanLiteral(true)).copiedFrom(e)
          let("ref" :: RefType, ref) { ref =>
            val ctNew = ClassType(ct.id, ct.tps.map(transform)).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform)).copiedFrom(e)
            let("alloc" :: UnitType(), MutableMapUpdate(TheHeap, ref, value).copiedFrom(e)) { _ =>
              ref
            }
          }

        case ClassSelector(recv, field) if erasesToRef(recv.getType) =>
          val recvTpe = classTypeInHeap(recv.getType.asInstanceOf[ClassType])
          val app = MutableMapApply(TheHeap, transform(recv)).copiedFrom(e)
          val aio = AsInstanceOf(app, recvTpe).copiedFrom(e)
          val iio = IsInstanceOf(app, recvTpe).copiedFrom(e)
          Assume(iio, ClassSelector(aio, field).copiedFrom(e)).copiedFrom(e)

        case FieldAssignment(recv, field, value) =>
          assert(erasesToRef(recv.getType))
          val recvTpe = classTypeInHeap(recv.getType.asInstanceOf[ClassType])
          smartLet("recv" :: RefType, transform(recv)) { recv =>
            val app = MutableMapApply(TheHeap, recv).copiedFrom(e)
            val aio = AsInstanceOf(app, recvTpe).copiedFrom(e)
            val iio = IsInstanceOf(app, recvTpe).copiedFrom(e)
            let("oldO" :: recvTpe, Assume(iio, aio).copiedFrom(e)) { oldO =>
              val newArgs = recvTpe.tcd.fields.map {
                case vd if vd.id == field => transform(value)
                case vd => ClassSelector(oldO, vd.id).copiedFrom(e)
              }
              val newO = ClassConstructor(recvTpe, newArgs).copiedFrom(e)
              MutableMapUpdate(TheHeap, recv, newO).copiedFrom(e)
            }
          }

        case _ => super.transform(e)
      }

      // TODO: Add discriminator pseudo-field so we can encode IsInstanceOf checks
      // override def transform(pat: Pattern): Pattern = pat match {
      //   case ClassPattern(binder, ct, subPats) =>
      //     ADTPattern(binder.map(transform), refSort.id, Seq.empty, subPats.map(transform))
      //       .copiedFrom(pat)
      //   case _ =>
      //     super.transform(pat)
      // }

      override def transform(tpe: Type): Type = tpe match {
        case ct: ClassType if erasesToRef(ct) =>
          RefType
        case FunctionType(_, _) =>
          val FunctionType(from, to) = super.transform(tpe)
          FunctionType(HeapType +: from, T(to, HeapType))
        // TODO: PiType
        case _ =>
          super.transform(tpe)
      }
    }

    // Represent state in a functional way
    object instrumenter extends StateInstrumenter {
      val trees: self.s.type = self.s

      // We use the adjusted symbols, so we can still invoke getType during instrumentation
      implicit val symbols: trees.Symbols = adjustedSymbols

      val stateTpe = HeapType
      def dummyState: Env = FiniteMap(Seq.empty, UnitLiteral(), HeapType.from, HeapType.to)

      override def instrument(e: Expr)(implicit pc: PurityCheck): MExpr = e match {
        case MutableMapApply(`TheHeap`, key) =>
          bind(instrument(key)) { vkey =>
            { s0 =>
              Uninstrum(
                MapApply(s0, vkey).copiedFrom(e),
                s0
              )
            }
          }

        case MutableMapUpdate(`TheHeap`, key, value) =>
          bind(instrument(key), instrument(value)) { (vkey, vvalue) =>
            { s0 =>
              Instrum(E(
                UnitLiteral().copiedFrom(e),
                MapUpdated(s0, vkey, vvalue).copiedFrom(e)
              ))
            }
          }

        case FunctionInvocation(id, targs, args) if isPureFunction(id) =>
          bindMany(args.map(instrument)) { vargs =>
            pure(FunctionInvocation(id, targs, vargs).copiedFrom(e))
          }

        case FunctionInvocation(id, targs, args) =>
          bindMany(args.map(instrument)) { vargs =>
            { s0 =>
              Instrum(FunctionInvocation(id, targs, s0 +: vargs).copiedFrom(e))
            }
          }

        case Lambda(params, body) =>
          val stateParam = freshStateParam().copiedFrom(e)
          val newBody = ensureInstrum(instrument(body)(pc)(stateParam.toVariable))
          val lam = Lambda(stateParam +: params, newBody).copiedFrom(e)
          pure(lam)

        case Application(callee, args) =>
          bind(instrument(callee)) { vcallee =>
            bindMany(args.map(instrument)) { vargs =>
              { s0 =>
                Instrum(Application(vcallee, s0 +: vargs).copiedFrom(e))
              }
            }
          }

        case Block(exprs, expr) =>
          bindMany(exprs.map(instrument)) { _ =>
            instrument(expr)
          }

        case Old(_) =>
          // Ignored here, but replaced separately later
          pure(e)

        case _ =>
          super.instrument(e)
      }
    }
  }
}
