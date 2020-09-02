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

    def freshStateParam(): ValDef = "s0" :: HeapType

    // TODO: Perform some effect analysis to omit some state parameters
    def adjustFunSig(fd: FunDef): FunDef = {
      val fdStripped = fd.copy(fullBody = exprOps.withBody(fd.fullBody, NoTree(fd.returnType)))
      val fdWithRefs = refTransformer.transform(fdStripped)
      val stateParam = freshStateParam().copiedFrom(fdWithRefs)
      val params = stateParam +: fdWithRefs.params
      val returnType = T(fdWithRefs.returnType, HeapType)
      fdWithRefs.copy(params = params, returnType = returnType)
    }

    // Compute symbols with modified signatures and added sorts. Only used during instrumentation.
    val adjustedSymbols: s.Symbols =
      context.symbols
        .withFunctions(context.symbols.functions.values.map(adjustFunSig).toSeq)
        .withSorts(Seq(refSort))

    def validHeapField(heap: Expr, key: Expr, tpe: Type): Expr =
      IsInstanceOf(MutableMapApply(heap, key), tpe)

    // Reduce all mutation to MutableMap updates
    // TODO: Handle mutable types other than classes
    object refTransformer extends SelfTreeTransformer {
      override def transform(e: Expr): Expr = e match {
        case ClassConstructor(ct, args) =>
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

        case ClassSelector(recv, field) =>
          val fieldTpe = e.getType
          val key = E(transform(recv), toHeapField(field)).copiedFrom(e)
          let("key" :: HeapType.from, key) { key =>
            val app = MutableMapApply(TheHeap, key).copiedFrom(e)
            val aio = Annotated(AsInstanceOf(app, fieldTpe).copiedFrom(e), Seq(Unchecked))
              .copiedFrom(e)
            Assume(validHeapField(TheHeap, key, fieldTpe).copiedFrom(e), aio).copiedFrom(e)
          }

        case FieldAssignment(recv, field, value) =>
          val key = E(transform(recv), toHeapField(field)).copiedFrom(e)
          MutableMapUpdate(TheHeap, key, transform(value)).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(tpe: Type): Type = tpe match {
        case ClassType(_, _) =>
          RefType
        case FunctionType(_, _) =>
          val FunctionType(from, to) = super.transform(tpe)
          FunctionType(HeapType +: from, to)
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

        case FunctionInvocation(id, targs, args) =>
          bindMany(args.map(instrument)) { vargs =>
            { s0 =>
              Instrum(FunctionInvocation(id, targs, s0 +: vargs).copiedFrom(e))
            }
          }

        // case Lambda(params, body) =>
        //   val stateParam = freshStateParam().copiedFrom(e)
        //   val newBody = ensureInstrum(instrument(body)(pc)(stateParam.toVariable))
        //   val lam = Lambda(stateParam +: params, newBody).copiedFrom(e)
        //   pure(lam)

        // case Application(callee, args) =>
        //   ???

        case Old(_) =>
          // Ignored here, but replaced separately later
          pure(e)

        case _ =>
          super.instrument(e)
      }
    }
  }
}
