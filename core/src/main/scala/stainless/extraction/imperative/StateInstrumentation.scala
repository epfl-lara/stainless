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

  protected lazy val HeapType: MapType = MapType(T(RefType, IntegerType()), AnyType())

  private[this] lazy val allocFieldId: Identifier = FreshIdentifier("alloc!")
  private[this] lazy val allocField: Expr = toHeapField(allocFieldId)

  private[this] def toHeapField(id: Identifier): Expr =
    IntegerLiteral(id.globalId) // FIXME: Cheap hack

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
    val adjustedSymbols: s.Symbols =
      context.symbols
        .withFunctions(context.symbols.functions.values.map(adjustFunSig).toSeq)
        .withSorts(Seq(refSort))

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
      override def transform(e: Expr): Expr = e match {
        case ClassConstructor(ct, args) if erasesToRef(ct) =>
          // TODO: Add mechanism to keep multiple freshly allocated objects apart
          val ref = Choose("ref" :: RefType, BooleanLiteral(true)).copiedFrom(e)
          let("ref" :: RefType, ref) { ref =>
            val updates = (allocField -> BooleanLiteral(true)) +:
              ct.tcd.fields.map(f => toHeapField(f.id)).zip(args.map(transform))
            Block(
              updates.map { case (field, arg) =>
                MutableMapUpdate(TheHeap, E(ref, field).copiedFrom(e), arg).copiedFrom(e)
              },
              ref
            ).copiedFrom(e)
          }

        case ClassSelector(recv, field) if erasesToRef(recv.getType) =>
          smartLet("recv" :: RefType, transform(recv)) { recv =>
            val key = E(recv, toHeapField(field)).copiedFrom(e)
            val app = MutableMapApply(TheHeap, key).copiedFrom(e)
            val fieldTpe = transform(e.getType)
            val aio = AsInstanceOf(app, fieldTpe).copiedFrom(e)
            Assume(validHeapField(TheHeap, key, fieldTpe).copiedFrom(e), aio).copiedFrom(e)
          }

        case FieldAssignment(recv, field, value) =>
          assert(erasesToRef(recv.getType))
          val key = E(transform(recv), toHeapField(field)).copiedFrom(e)
          MutableMapUpdate(TheHeap, key, transform(value)).copiedFrom(e)

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
