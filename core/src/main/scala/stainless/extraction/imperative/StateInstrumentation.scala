/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait StateInstrumentation extends oo.CachingPhase { self =>
  val s: Trees
  val t: s.type

  import s._
  // import exprOps._
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

  private[this] lazy val HeapType: MapType = MapType(T(RefType, IntegerType()), AnyType())

  private[this] lazy val allocFieldId: Identifier = FreshIdentifier("alloc!")
  private[this] lazy val allocField: Expr = toHeapField(allocFieldId)

  private[this] def toHeapField(id: Identifier): Expr =
    IntegerLiteral(id.globalId) // FIXME: Cheap hack
  private[this] def getHeapField(heap: Expr, ref: Expr, field: Expr): Expr =
    MapApply(heap, E(ref, field))
  private[this] def updateHeapField(heap: Expr, ref: Expr, field: Expr, value: Expr): Expr =
    MapUpdated(heap, E(ref, field), value)

  // A sentinel value for the first transformation
  private[this] lazy val TheHeap = NoTree(HeapType)

  /* Instrumentation */

  protected type TransformerContext <: InstrumentationContext

  trait InstrumentationContext { context: TransformerContext =>
    implicit val symbols: s.Symbols

    def adjustType(tpe: Type): Type = typeOps.postMap {
      case ClassType(_, _) =>
        Some(RefType)
      case _ =>
        None
    }(tpe)

    // TODO: Perform some effect analysis to omit some state parameters
    def adjustFunSig(fd: FunDef): FunDef = {
      val params = ("state" :: HeapType) +: fd.params
      // val params = ("state" :: HeapType) +: fd.params.map(vd => vd.copy(tpe = adjustType(vd.tpe)))
      val returnType = T(adjustType(fd.returnType), HeapType)
      // fd.copy(params = params, returnType = returnType)
      val newFd = fd.copy(
        params = params,
        returnType = returnType,
        fullBody = exprOps.withBody(fd.fullBody, NoTree(returnType)))
      refTransformer.transform(newFd)
    }

    // Compute symbols with modified signatures and added sorts
    val adjustedSymbols: s.Symbols =
      context.symbols
        .withFunctions(context.symbols.functions.values.map(adjustFunSig).toSeq)
        .withSorts(Seq(refSort))

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
          val key = E(transform(recv), toHeapField(field)).copiedFrom(e)
          val app = MutableMapApply(TheHeap, key).copiedFrom(e)
          Annotated(AsInstanceOf(app, e.getType).copiedFrom(e), Seq(Unchecked)).copiedFrom(e)
        case FieldAssignment(recv, field, value) =>
          val key = E(transform(recv), toHeapField(field)).copiedFrom(e)
          MutableMapUpdate(TheHeap, key, transform(value)).copiedFrom(e)
        case _ => super.transform(e)
      }

      override def transform(tpe: Type): Type = tpe match {
        case ClassType(_, _) => RefType
        case _ => super.transform(tpe)
      }
    }

    // Represent state in a functional way
    object instrumenter extends StateInstrumenter {
      val trees: self.s.type = self.s

      // We Use the adjusted symbols, so we can still invoke getType during instrumentation
      implicit val symbols: trees.Symbols = adjustedSymbols

      val stateTpe = HeapType
      def dummyState: Env = FiniteMap(Seq.empty, UnitLiteral(), HeapType.from, HeapType.to)

      override def instrument(e: Expr)(implicit pc: PurityCheck): MExpr = e match {
        case MutableMapApply(`TheHeap`, key) =>
          val Tuple(Seq(recv, field)) = key
          bind(instrument(recv)) { vrecv =>
            { s0 =>
              Uninstrum(
                MapApply(s0, E(vrecv, field).copiedFrom(key)).copiedFrom(e),
                s0
              )
            }
          }
        case MutableMapUpdate(`TheHeap`, key, value) =>
          val Tuple(Seq(recv, field)) = key
          bind(instrument(recv), instrument(value)) { (vrecv, vvalue) =>
            { s0 =>
              Instrum(E(
                UnitLiteral().copiedFrom(e),
                MapUpdated(s0, E(vrecv, field).copiedFrom(key), vvalue).copiedFrom(e)
              ))
            }
          }
        // case ClassConstructor(ct, args) =>
        //   bindMany(args.map(instrument)) { vargs =>
        //     { s0 =>
        //       // TODO: Add mechanism to keep multiple freshly allocated objects apart
        //       val ref = Choose("ref" :: RefType, BooleanLiteral(true)).copiedFrom(e)
        //       Instrum(
        //         let("ref" :: RefType, ref) { ref =>
        //           val updates = (allocField -> BooleanLiteral(true)) +:
        //             ct.tcd.fields.map(f => toHeapField(f.id)).zip(vargs)
        //           val s1 = updates.foldLeft(s0) { case (s, (field, arg)) =>
        //             updateHeapField(s, ref, field, arg).copiedFrom(e)
        //           }
        //           let("upd" :: HeapType, s1) { s1 =>
        //             E(ref, s1).copiedFrom(e)
        //           }.copiedFrom(e)
        //         }
        //       )
        //     }
        //   }
        // case ClassSelector(recv, field) =>
        //   bind(instrument(recv)) { vrecv =>
        //     { s0 =>
        //       Uninstrum(
        //         getHeapField(s0, vrecv, toHeapField(field)).copiedFrom(e),
        //         s0
        //       )
        //     }
        //   }
        // case FieldAssignment(recv, field, value) =>
        //   bind(instrument(recv), instrument(value)) { (vrecv, vvalue) =>
        //     { s0 =>
        //       Instrum(E(
        //         UnitLiteral().copiedFrom(e),
        //         updateHeapField(s0, vrecv, toHeapField(field), vvalue).copiedFrom(e)
        //       ).copiedFrom(e))
        //     }
        //   }

        case FunctionInvocation(id, targs, args) =>
          bindMany(args.map(instrument)) { vargs =>
            { s0 =>
              Instrum(FunctionInvocation(id, targs, s0 +: vargs).copiedFrom(e))
            }
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
