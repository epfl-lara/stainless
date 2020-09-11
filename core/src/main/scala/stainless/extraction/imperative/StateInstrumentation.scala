/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait StateInstrumentation extends oo.CachingPhase with utils.SyntheticSorts { self =>
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
  private[this] lazy val TheHeap = NoTree(MutableMapType(HeapType.from, HeapType.to))

  private[this] lazy val unapplyId = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)

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
      import OptionSort._
      val syms = context.symbols
      val unapplyFds = syms.classes.values.toSeq.map(makeClassUnapply).flatten
      syms
        .withFunctions(unapplyFds ++ syms.functions.values.map(adjustFunSig).toSeq)
        .withSorts(Seq(refSort) ++ syms.sorts.values.map(refTransformer.transform).toSeq)
        .withClasses(syms.classes.values.map(refTransformer.transform).toSeq)
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
      if (!symbols.mutableClasses.contains(cd.id))
        return None

      import OptionSort._
      Some(mkFunDef(unapplyId(cd.id), t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get))(
          cd.typeArgs.map(_.id.name) : _*) { tparams =>
        val tcd = cd.typed(tparams)
        val ct = tcd.toType
        val objTpe = classTypeInHeap(ct)

        val base = RefType
        // def condition(ref: Expr): Expr = IsInstanceOf(MutableMapApply(TheHeap, ref), objTpe)

        // val baseReturnType = TupleType(tcd.fields.map(_.tpe))
        // val vd = t.ValDef.fresh("v", baseReturnType)
        // val returnType = t.RefinementType(vd, condition(vd.toVariable))
        val returnType = objTpe

        (Seq("s0" :: HeapType, "x" :: base), T(option)(returnType), { case Seq(s0, x) =>
          val body =
            if_ (IsInstanceOf(MutableMapApply(TheHeap, x), objTpe)) {
              C(some)(returnType)(AsInstanceOf(MutableMapApply(TheHeap, x), objTpe))
            } else_ {
              C(none)(returnType)()
            }
          instrumenter.instrumentPure(body, s0)
        })
      })
    }

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
            val ctNew = ClassType(ct.id, ct.tps.map(transform)).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform)).copiedFrom(e)
            let("alloc" :: UnitType(), MutableMapUpdate(TheHeap, ref, value).copiedFrom(e)) { _ =>
              ref
            }
          }

        case ClassSelector(recv, field) if erasesToRef(recv.getType) =>
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)
          smartLet("recv" :: RefType, transform(recv)) { recvRef =>
            ClassSelector(valueFromHeap(recvRef, objTpe, e), field).copiedFrom(e)
          }

        case FieldAssignment(recv, field, value) =>
          assert(erasesToRef(recv.getType))
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

        case IsInstanceOf(recv, tpe) if erasesToRef(tpe) =>
          val ct = tpe.asInstanceOf[ClassType]
          val app = MutableMapApply(TheHeap, transform(recv)).copiedFrom(e)
          IsInstanceOf(app, classTypeInHeap(ct)).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(pat: Pattern): Pattern = pat match {
        case ClassPattern(binder, ct, subPats) if erasesToRef(ct) =>
          UnapplyPattern(binder.map(transform), Seq(TheHeap),
            unapplyId(ct.id),
            ct.tps.map(transform),
            subPats.map(transform)
          ).copiedFrom(pat)
        case _ =>
          super.transform(pat)
      }

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

      override def transform(cd: ClassDef): ClassDef = {
        val env = initEnv
        // FIXME: Transform type arguments in parents?
        new ClassDef(
          transform(cd.id, env),
          cd.tparams.map(transform(_, env)),
          cd.parents,  // don't transform parents
          cd.fields.map(transform(_, env)),
          cd.flags.map(transform(_, env))
        ).copiedFrom(cd)
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

      override def instrument(pat: Pattern, s0: Expr): Pattern = pat match {
        case pat @ UnapplyPattern(_, Seq(`TheHeap`), _, _, subPats) =>
          val newSubPats = subPats.map(p => instrument(p, s0))
          pat.copy(recs = Seq(s0), subPatterns = newSubPats).copiedFrom(pat)
        case PatternExtractor(subPats, recons) =>
          recons(subPats.map(p => instrument(p, s0)))
      }
    }
  }
}
