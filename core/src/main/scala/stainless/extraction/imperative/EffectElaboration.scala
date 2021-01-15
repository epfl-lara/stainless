/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position

object optCheckHeapContracts extends inox.FlagOptionDef("check-heap-contracts", true)

// TODO(gsps): Ghost annotations are currently unchecked. Should be able to reuse `GhostChecker`.
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

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols,
      functions: Seq[FunctionResult]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected final type ClassResult = (t.ClassDef, Option[t.FunDef])
  override protected final def registerClasses(symbols: t.Symbols,
      classResults: Seq[ClassResult]): t.Symbols = {
    val (classes, unapplyFds) = classResults.unzip
    symbols.withClasses(classes).withFunctions(unapplyFds.flatten)
  }

  protected class TransformerContext(val symbols: Symbols) extends RefTransformContext

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  override protected def extractSymbols(tctx: TransformerContext, symbols: s.Symbols): t.Symbols = {
    // We filter out the definitions related to AnyHeapRef since they are only needed for inferring
    // which types live on the heap.
    val newSymbols = NoSymbols
      .withFunctions(symbols.functions.values.filterNot(fd => hasFlag(fd, "refEq")).toSeq)
      .withClasses(symbols.classes.values.filterNot(cd => hasFlag(cd, "anyHeapRef")).toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    super.extractSymbols(tctx, newSymbols)
      .withSorts(Seq(heapRefSort) ++ OptionSort.sorts(newSymbols))
      .withFunctions(Seq(dummyHeap) ++ OptionSort.functions(newSymbols))
      // .withSorts(Seq(heapRefSort, heapSort) ++ OptionSort.sorts(newSymbols))
      // .withFunctions(heapFunctions ++ OptionSort.functions(newSymbols))
  }

  override protected def extractFunction(tctx: TransformerContext, fd: FunDef): FunctionResult =
    tctx.transformFun(fd)

  override protected def extractSort(tctx: TransformerContext, sort: ADTSort): ADTSort =
    tctx.typeOnlyRefTransformer.transform(sort)

  override protected def extractClass(tctx: TransformerContext, cd: ClassDef): ClassResult =
    (tctx.typeOnlyRefTransformer.transform(cd), tctx.makeClassUnapply(cd))
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

/*
trait SyntheticHeapFunctions { self =>
  val s: Trees
  val t: s.trees

  import t._
  import dsl._

  protected lazy val heapReadId: Identifier = ast.SymbolIdentifier("stainless.lang.HeapRef.read")
  protected lazy val heapModifyId: Identifier = ast.SymbolIdentifier("stainless.lang.HeapRef.modify")

  protected def heapFunctions: Seq[FunDef] = {
    val readFd = mkFunDef(heapReadId, Unchecked, Synthetic, Inline)() { _ =>
      (Seq("heap" :: HeapType, "x" :: HeapRefType), AnyType(), {
        case Seq(heap, x) =>
          Require(
            heap.select(heapReadableId).contains(x),
            MapApply(heap.select(heapMapId), x)
          )
      })
    }
    val modifyFd = mkFunDef(heapModifyId, Unchecked, Synthetic, Inline)() { _ =>
      (Seq("heap" :: HeapType, "x" :: HeapRefType, "v" :: AnyType()), UnitType(), {
        case Seq(heap, x) =>
          Require(
            heap.select(heapModifiableId).contains(x),
            heapWithMap(heap, MapUpdated(heap.select(heapMapId), x, v))
          )
      })
    }
    Seq(readFd, modifyFd)
  }

  protected def heapWithMap(oldHeap: Expr, newMap: Expr): Expr =
    C(heapCons)(
      newMap,
      oldHeap.select(heapReadableId),
      oldHeap.select(heapModifiableId)
    )
}
*/

trait RefTransform extends oo.CachingPhase with utils.SyntheticSorts /*with SyntheticHeapFunctions*/ { self =>
  val s: Trees
  val t: s.type

  import s._
  import dsl._

  /* Heap encoding */

  protected lazy val unapplyId = new utils.ConcurrentCached[Identifier, Identifier](_.freshen)
  protected lazy val innerId = new utils.ConcurrentCached[Identifier, Identifier](
    id => FreshIdentifier(s"${id.name}__inner")
  )

  /* The transformer */

  protected type TransformerContext <: RefTransformContext

  trait RefTransformContext { context: TransformerContext =>
    implicit val symbols: s.Symbols

    lazy val HeapRefSetType: Type = SetType(HeapRefType)
    lazy val EmptyHeapRefSet: Expr = FiniteSet(Seq.empty, HeapRefType)

    // This caches whether types live in the heap or not
    lazy val livesInHeap = new utils.ConcurrentCached[Type, Boolean](isHeapType(_))

    protected lazy val effectLevel = new utils.ConcurrentCached[Identifier, exprOps.EffectLevel]({
      id => exprOps.getEffectLevel(symbols.getFunction(id))
    })

    private def isHeapType(tpe: Type): Boolean = tpe match {
      case AnyHeapRef() => true
      // We lookup the parents through the cache so that the hierarchy is traversed at most once
      case ct: ClassType => ct.tcd.parents.exists(a => livesInHeap(a.toType))
      case _ => false
    }

    private def freshStateParam(): ValDef = "heap0" :: HeapType
    private def freshRefSetVd(name: String): ValDef = name :: HeapRefSetType

    def smartLet(vd: => ValDef, e: Expr)(f: Expr => Expr): Expr = e match {
      case _: Terminal => f(e)
      case _ => let(vd, e)(f)
    }
    def classTypeInHeap(ct: ClassType): ClassType =
      ClassType(ct.id, ct.tps.map(typeOnlyRefTransformer.transform)).copiedFrom(ct)

    def makeClassUnapply(cd: ClassDef): Option[FunDef] = {
      if (!livesInHeap(cd.typed.toType))
        return None

      import OptionSort._
      Some(mkFunDef(unapplyId(cd.id), t.DropVCs, t.Synthetic, t.IsUnapply(isEmpty, get))(
          cd.typeArgs.map(_.id.name) : _*) { tparams =>
        val tcd = cd.typed(tparams)
        val ct = tcd.toType
        val objTpe = classTypeInHeap(ct)

        (
          Seq("heap" :: HeapType, "readsDom" :: HeapRefSetType, "x" :: HeapRefType),
          T(option)(objTpe),
          { case Seq(heap, readsDom, x) =>
            Require(
              ElementOfSet(x, readsDom),
              if_ (IsInstanceOf(MapApply(heap, x), objTpe)) {
                C(some)(objTpe)(AsInstanceOf(MapApply(heap, x), objTpe))
              } else_ {
                C(none)(objTpe)()
              }
            )
          }
        )
      } .copiedFrom(cd))
    }

    // Reduce all mutation to assignments of a local heap variable
    // TODO: Handle mutable types other than classes
    abstract class RefTransformer extends oo.DefinitionTransformer {
      val s: self.s.type = self.s
      val t: self.s.type = self.s

      override def transform(tpe: Type, env: Env): Type = tpe match {
        case ct: ClassType if livesInHeap(ct) =>
          HeapRefType
        case FunctionType(_, _) =>
          val FunctionType(from, to) = super.transform(tpe, env)
          FunctionType(HeapType +: from, T(to, HeapType))
        // TODO: PiType
        case _ =>
          super.transform(tpe, env)
      }

      override def transform(cd: ClassDef): ClassDef = {
        val env = initEnv
        // FIXME: Transform type arguments in parents?

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

    object typeOnlyRefTransformer extends RefTransformer {
      override final type Env = Unit
      override final val initEnv: Unit = ()

      def transform(tpe: Type): Type = transform(tpe, ())
      def transform(vd: ValDef): ValDef = transform(vd, ())
      def transform(td: TypeParameterDef): TypeParameterDef = transform(td, ())
      def transform(flag: Flag): Flag = transform(flag, ())
    }

    object funRefTransformer extends RefTransformer {
      private lazy val dummyHeapVd: ValDef = "dummyHeap" :: HeapType

      case class Env(
        readsVdOpt: Option[ValDef],
        modifiesVdOpt: Option[ValDef],
        heapVdOpt: Option[ValDef])
      {
        def expectHeapVd(pos: Position, usage: String) =
          heapVdOpt getOrElse {
            self.context.reporter.error(pos, s"Cannot use heap-accessing construct ($usage) here")
            dummyHeapVd
          }

        def expectReadsV(pos: Position, usage: String) =
          readsVdOpt.map(_.toVariable) getOrElse {
            self.context.reporter.error(pos, s"Cannot $usage without a reads clause")
            EmptyHeapRefSet
          }

        def expectModifiesV(pos: Position, usage: String) =
          modifiesVdOpt.map(_.toVariable) getOrElse {
            self.context.reporter.error(pos, s"Cannot $usage without a modifies clause")
            EmptyHeapRefSet
          }

        def noModifications = copy(modifiesVdOpt = None)
        def writeAllowed = modifiesVdOpt.isDefined
      }

      def initEnv: Env = ???  // unused

      def valueFromHeap(recv: Expr, objTpe: ClassType, heapVd: ValDef, fromE: Expr): Expr = {
        val app = MapApply(heapVd.toVariable, recv).copiedFrom(fromE)
        val aio = AsInstanceOf(app, objTpe).copiedFrom(fromE)
        val iio = IsInstanceOf(app, objTpe).copiedFrom(fromE)
        Assume(iio, aio).copiedFrom(fromE)
      }

      def checkedRecv(recv: Expr, inSet: Expr, msg: String, result: Expr, fromE: Expr): Expr =
        Assert(ElementOfSet(recv, inSet).copiedFrom(fromE), Some(msg), result).copiedFrom(fromE)

      override def transform(e: Expr, env: Env): Expr = e match {
        // Reference equality is transformed into value equality on references
        case RefEq(e1, e2) =>
          Equals(transform(e1, env), transform(e2, env)).copiedFrom(e)

        case ClassConstructor(ct, args) if livesInHeap(ct) =>
          // TODO: Add mechanism to keep freshly allocated objects apart from older ones
          val heapVd = env.expectHeapVd(e.getPos, "allocate heap object")
          val ref = Choose("ref" :: HeapRefType, BooleanLiteral(true)).copiedFrom(e)
          let("ref" :: HeapRefType, ref) { ref =>
            val ctNew = ClassType(ct.id, ct.tps.map(transform(_, env))).copiedFrom(ct)
            val value = ClassConstructor(ctNew, args.map(transform(_, env))).copiedFrom(e)
            val newHeap = MapUpdated(heapVd.toVariable, ref, value).copiedFrom(e)
            let("alloc" :: UnitType(), Assignment(heapVd.toVariable, newHeap).copiedFrom(e)) { _ =>
              ref
            }
          }

        case ClassSelector(recv, field) if livesInHeap(recv.getType) =>
          val heapVd = env.expectHeapVd(e.getPos, "read from heap object")
          val readsDom = env.expectReadsV(e.getPos, "read from heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)

          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val sel = ClassSelector(valueFromHeap(recvRef, objTpe, heapVd, e), field).copiedFrom(e)
            checkedRecv(recvRef, readsDom, "read object in reads set", sel, e)
          }

        case FieldAssignment(recv, field, value) if livesInHeap(recv.getType) =>
          if (!env.writeAllowed)
            self.context.reporter.error(e.getPos, "Can't modify heap in read-only context")

          val heapVd = env.expectHeapVd(e.getPos, "write to heap object")
          val modifiesDom = env.expectModifiesV(e.getPos, "write to heap object")
          val ct = recv.getType.asInstanceOf[ClassType]
          val objTpe = classTypeInHeap(ct)

          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val oldObj = valueFromHeap(recvRef, objTpe, heapVd, e)
            let("oldObj" :: objTpe, oldObj) { oldObj =>
              val newCt = objTpe.asInstanceOf[ClassType]
              val newArgs = newCt.tcd.fields.map {
                case vd if vd.id == field => transform(value, env)
                case vd => ClassSelector(oldObj, vd.id).copiedFrom(e)
              }
              val newObj = ClassConstructor(newCt, newArgs).copiedFrom(e)
              val newHeap = MapUpdated(heapVd.toVariable, recvRef, newObj).copiedFrom(e)
              val assgn = Assignment(heapVd.toVariable, newHeap).copiedFrom(e)
              checkedRecv(recvRef, modifiesDom, "modified object in modifies set", assgn, e)
            }
          }

        case IsInstanceOf(recv, tpe) if livesInHeap(tpe) =>
          val heapVd = env.expectHeapVd(e.getPos, "runtime type-check on heap object")
          val readsDom = env.expectReadsV(e.getPos, "runtime type-check heap object")
          val ct = tpe.asInstanceOf[ClassType]

          smartLet("recv" :: HeapRefType, transform(recv, env)) { recvRef =>
            val app = MapApply(heapVd.toVariable, recvRef).copiedFrom(e)
            val iio = IsInstanceOf(app, classTypeInHeap(ct)).copiedFrom(e)
            checkedRecv(recvRef, readsDom, "runtime type-checked object in reads set", iio, e)
          }

        case fi @ FunctionInvocation(id, targs, vargs) =>
          val targs1 = targs.map(transform(_, env))
          val vargs1 = vargs.map(transform(_, env))

          effectLevel(id) match {
            case None =>
              FunctionInvocation(id, targs1, vargs1).copiedFrom(e)

            case Some(writes) =>
              val heapVd = env.expectHeapVd(e.getPos, "effectful function call")
              val readsDom = env.expectReadsV(e.getPos, "call heap-reading function")
              lazy val modifiesDom = env.expectModifiesV(e.getPos, "call heap-modifying function")

              val extraArgs = Seq(heapVd.toVariable, readsDom) ++
                (if (writes) Some(modifiesDom) else None)
              val call = FunctionInvocation(id, targs1, extraArgs ++ vargs1).copiedFrom(e)

              if (writes) {
                // Update the local heap variable and project out the the function result
                val resTpe = T(typeOnlyRefTransformer.transform(fi.tfd.returnType), HeapType)
                let("res" :: resTpe, call) { res =>
                  Block(
                    Seq(Assignment(heapVd.toVariable, res._2).copiedFrom(e)),
                    res._1
                  ).copiedFrom(e)
                }
              } else {
                // Nothing to be done, if the callee only reads from but does not write to the heap
                call
              }
          }

        case e: Old =>
          // Will be translated separately in postconditions
          // TODO(gsps): Add ability to refer back to old state snapshots for any ghost code
          e

        case _ => super.transform(e, env)
      }

      override def transform(pat: Pattern, env: Env): Pattern = pat match {
        case ClassPattern(binder, ct, subPats) if livesInHeap(ct) =>
          val heapVd = env.expectHeapVd(pat.getPos, "class pattern unapply")
          val readsDom = env.expectReadsV(pat.getPos, "call heap-reading unapply")
          val newClassPat = ClassPattern(
            None,
            classTypeInHeap(ct),
            subPats.map(transform(_, env))
          ).copiedFrom(pat)
          UnapplyPattern(
            binder.map(transform(_, env)),
            Seq(heapVd.toVariable, readsDom),
            unapplyId(ct.id),
            ct.tps.map(transform(_, env)),
            Seq(newClassPat)
          ).copiedFrom(pat)
        case _ =>
          super.transform(pat, env)
      }
    } // << funRefTransformer

    def transformFun(fd: FunDef): Seq[FunDef] = {
      import exprOps._

      val level = effectLevel(fd.id)
      val reads = level.isDefined
      val writes = level.getOrElse(false)

      val heapVdOpt0 = if (reads) Some(freshStateParam()) else None
      val readsDomVdOpt = if (reads) Some(freshRefSetVd("readsDom")) else None
      val modifiesDomVdOpt = if (writes) Some(freshRefSetVd("modifiesDom")) else None
      val newRealParams = fd.params.map(typeOnlyRefTransformer.transform)
      val newParams = Seq(heapVdOpt0, readsDomVdOpt, modifiesDomVdOpt).flatten ++ newRealParams

      val newReturnType = {
        val newReturnType1 = typeOnlyRefTransformer.transform(fd.returnType)
        if (writes) T(newReturnType1, HeapType) else newReturnType1
      }

      // Let-bindings to this function's `reads` and `modifies` contract sets
      val readsVdOpt = if (reads) Some(freshRefSetVd("reads")) else None
      val modifiesVdOpt = if (writes) Some(freshRefSetVd("modifies")) else None

      def specEnv(heapVdOpt: Option[ValDef], readsVdOpt: Option[ValDef] = readsVdOpt) =
        funRefTransformer.Env(readsVdOpt, modifiesVdOpt = None, heapVdOpt)
      def bodyEnv(heapVdOpt: Option[ValDef]) =
        funRefTransformer.Env(readsVdOpt, modifiesVdOpt, heapVdOpt)

      // Transform postcondition body
      def transformPost(post: Expr, resVd: ValDef, valueVd: ValDef,
                        heapVdOpt0: Option[ValDef], heapVdOpt1: Option[ValDef]): Expr =
      {
        val replaceRes = resVd != valueVd
        // Rewrite the value result variable (used if `resVd` now also contains the heap state)
        val post1 = postMap {
          case v: Variable if replaceRes && v.id == resVd.id =>
            Some(valueVd.toVariable.copiedFrom(v))
          case _ =>
            None
        }(post)
        // Transform postcondition body in post-state (ignoring `old(...)` parts)
        val post2 = funRefTransformer.transform(post1, specEnv(heapVdOpt1))
        // Transform `old(...)` parts of postcondition body in pre-state
        postMap {
          case Old(e) =>
            Some(funRefTransformer.transform(e, specEnv(heapVdOpt0)))
          case _ =>
            None
        }(post2)
      }

      // Unpack specs from the existing function
      val specced = BodyWithSpecs(fd.fullBody)

      // Transform existing specs
      val newSpecsMap: Map[SpecKind, Specification] = specced.specs.map {
        case spec @ Postcondition(lam @ Lambda(Seq(resVd), post)) =>
          val (resVd1, post1) = if (writes) {
            val valueVd: ValDef = "resV" :: resVd.tpe
            val heapVd1: ValDef = "heap1" :: HeapType
            val resVd1 = resVd.copy(tpe = T(resVd.tpe, HeapType))
            val post1 = Let(valueVd, resVd1.toVariable._1,
              Let(heapVd1, resVd1.toVariable._2,
                transformPost(post, resVd, valueVd, heapVdOpt0, Some(heapVd1))))
            (resVd1, post1)
          } else {
            (resVd, transformPost(post, resVd, resVd, heapVdOpt0, heapVdOpt0))
          }
          val newSpec = Postcondition(Lambda(Seq(resVd1), post1).copiedFrom(lam))
          (spec.kind, newSpec.setPos(spec.getPos))

        case spec =>
          val newSpec = spec.transform(expr =>
            funRefTransformer.transform(expr, specEnv(heapVdOpt0)))
          (spec.kind, newSpec)
      } .toMap

      // Transform reads spec in a way that doesn't depend on `readsVdOpt`
      val newUncheckedReadsExpr = specced.specs.collectFirst {
        case spec: ReadsContract =>
          val env = specEnv(heapVdOpt0, readsVdOpt = readsDomVdOpt) // Just use `readsDom` instead.
          val newExpr = spec.transform(expr => funRefTransformer.transform(expr, env))
            .asInstanceOf[ReadsContract].expr
          Annotated(newExpr, Seq(DropVCs)).copiedFrom(newExpr)
      } .getOrElse(EmptyHeapRefSet)

      // Translate `reads` and `modifies` into additional precondition
      val newSpecs: Seq[Specification] = Seq(
        newSpecsMap.get(PostconditionKind),
        Some(newSpecsMap
          .getOrElse(PreconditionKind, Precondition(BooleanLiteral(true)))
          .transform { expr =>
            andJoin(Seq(
              Some(expr),
              readsVdOpt.map(r =>
                SubsetOf(r.toVariable, readsDomVdOpt.get.toVariable).copiedFrom(r)),
              modifiesVdOpt.map(m =>
                SubsetOf(m.toVariable, modifiesDomVdOpt.get.toVariable).copiedFrom(m))
            ).flatten)
          }),
        newSpecsMap.get(MeasureKind),
      ).flatten

      // Transform implementation body (which becomes the inner function, if needed)
      val innerBodyOpt: Option[Expr] = specced.bodyOpt.map { body =>
        if (writes) {
          // Add a locally mutable heap binding
          val heapVd: ValDef = "heap" :: HeapType
          val innerNewBody = funRefTransformer.transform(body, bodyEnv(heapVdOpt = Some(heapVd)))
          LetVar(heapVd, heapVdOpt0.get.toVariable,
            E(innerNewBody, heapVd.toVariable))
        } else {
          // Simply transform with pre-state everywhere
          funRefTransformer.transform(body, bodyEnv(heapVdOpt = heapVdOpt0))
        }
      }

      // Rebuild full body, potentially adding bindings for `reads` and `modifies` sets
      def wrapHeapContractBindings(body: Expr, readsExpr: => Expr, modifiesExpr: => Expr): Expr = {
        def maybeLetWrap(vdOpt: Option[ValDef], value: => Expr, body: Expr): Expr =
          vdOpt match {
            case Some(vd) => Let(vd, value, body).copiedFrom(body)
            case None => body
          }

        maybeLetWrap(readsVdOpt, readsExpr,
          maybeLetWrap(modifiesVdOpt, modifiesExpr,
            body))
      }

      val newTParams = fd.tparams.map(typeOnlyRefTransformer.transform)
      val newFlags = fd.flags.map(typeOnlyRefTransformer.transform)

      def makeOuterFd(bodyOpt: Option[Expr], freshen: Boolean): FunDef = {
        val fullBody = wrapHeapContractBindings(
          specced.withBody(bodyOpt, newReturnType).copy(specs = newSpecs).reconstructed,
          readsExpr = newUncheckedReadsExpr,
          modifiesExpr = newSpecsMap.get(ModifiesKind)
            .map(_.asInstanceOf[ModifiesContract].expr).getOrElse(EmptyHeapRefSet)
        )
        new FunDef(
          fd.id,
          newTParams,
          newParams,
          newReturnType,
          if (freshen) freshenLocals(fullBody) else fullBody,
          newFlags
        ).copiedFrom(fd)
      }

      if (reads) {
        // If a function involves the heap we split it into
        // - an outer function that projects the heap according to the reads and modifies clauses,
        // - an inner function containing the implementation.
        // The outer function inherits all the specs, whereas the inner function will be unchecked.
        val outerBody1 = {
          val heapArg = MapMerge(
            readsVdOpt.get.toVariable,
            heapVdOpt0.get.toVariable,
            E(dummyHeap.id)()
          ).copiedFrom(fd)
          val fi = FunctionInvocation(
            innerId(fd.id),
            newTParams.map(_.tp),
            Seq(heapArg, readsVdOpt.get.toVariable) ++ modifiesVdOpt.map(_.toVariable) ++
              newRealParams.map(_.toVariable)
          ).copiedFrom(fd)

          if (writes) {
            let("res" :: newReturnType, fi) { res =>
              E(
                res._1,
                MapMerge(
                  modifiesVdOpt.get.toVariable,
                  res._2,
                  heapVdOpt0.get.toVariable
                ).copiedFrom(fd)
              )
            }
          } else {
            fi
          }
        }

        // We duplicate the reads clause to compensate for it being unchecked in `makeOuterFd`.
        // This solves an issue with bootstrapping reads checks: The reads clause should be subject
        // to its own restrictions (i.e., it must not read outside the reads clause), but we cannot
        // refer to `readsVdOpt` while defining it. Instead, we first translate the reads clause
        // without checks in `makeOuterFd` and insert an additional, checked copy here.
        val outerBody2 = newSpecsMap.get(ReadsKind) match {
          case Some(newReadsSpec) =>
            val newReadsExpr = newReadsSpec.asInstanceOf[ReadsContract].expr
            Block(Seq(newReadsExpr), outerBody1).copiedFrom(outerBody1)
          case None =>
            outerBody1
        }

        val outerFd = {
          val fd = makeOuterFd(Some(outerBody2), freshen = true)
          // FIXME: Reads and modifies should be checked even for extern functions.
          val extraFlags = if (newFlags.contains(Extern)) Seq(t.DropVCs) else Seq.empty
          fd.copy(
            flags = (newFlags.filterNot(_ == Extern) ++ extraFlags ++ Seq(InlineOnce)).distinct)
        }

        val innerFd = {
          val fullBody = wrapHeapContractBindings(
            innerBodyOpt.getOrElse(NoTree(newReturnType).copiedFrom(fd)),
            readsExpr = readsDomVdOpt.get.toVariable,
            modifiesExpr = modifiesDomVdOpt.map(_.toVariable).getOrElse(EmptyHeapRefSet))

          val extraFlags =
            if (newFlags.contains(Extern)) Seq.empty
            else Seq(t.Synthetic, t.DropVCs, t.ImplPrivate)

          freshenSignature(outerFd.copy(
            id = innerId(fd.id),
            fullBody = fullBody,
            flags = (newFlags ++ extraFlags).distinct
          ).copiedFrom(fd))
        }

        Seq(outerFd, innerFd)

      } else {
        // Pure functions are merely ref-transformed.
        Seq(makeOuterFd(innerBodyOpt, freshen = false))
      }
    }
  }
}
