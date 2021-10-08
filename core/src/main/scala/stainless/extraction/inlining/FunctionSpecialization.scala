/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package inlining

object DebugSectionFunctionSpecialization extends inox.DebugSection("fun-specialization")

class FunctionSpecialization(override val s: Trees)(override val t: s.type)
                            (using override val context: inox.Context)
  extends CachingPhase
     with IdentitySorts { self =>
  import s._

  given givenDebugSection: DebugSectionFunctionSpecialization.type = DebugSectionFunctionSpecialization

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult](
    (fd, symbols) => getDependencyKey(fd.id)(using symbols)
  )

  override protected type FunctionResult = Option[t.FunDef]
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private val helperMsg =
    "Specialization requires parameters of the new function to be passed in a " +
    "one-to-one correspondence with the original parameters, with the exception of " +
    "specialized parameters and fresh parameters. For specialized parameters, " +
    "arguments must be expressions referring only to parameters that do not vary in " +
    "recursive calls. Fresh parameters may be added at the end of the parameter list " +
    "and are passed through recursive calls, so they can be used in specialization " +
    "arguments."

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): Option[t.FunDef] = {
    import symbols.{given, _}
    import exprOps._

    if (fd.flags.contains(Template))
      return None

    object SpecializeCall {
      def unapply(e: Expr): Option[FunctionInvocation] = e match {
        case FunctionInvocation(
          ast.SymbolIdentifier("stainless.lang.specialize"),
          Seq(_),
          Seq(fi: FunctionInvocation)
        ) => Some(fi)
        case _ => None
      }
    }

    def check(expr: Expr): Unit =
      exprOps.preTraversal {
        case specFi @ SpecializeCall(_) =>
          context.reporter.fatalError(specFi.getPos,
            "The `specialize` construct must currently be used directly as the body of a function")
        case fi: FunctionInvocation if fi.tfd.flags.contains(Template) =>
          context.reporter.fatalError(fi.getPos,
            "Cannot call an `@template` function directly, since it will be removed.")
        case _ =>
      }(expr)

    class Specializer(
      origFd: FunDef,
      newId: Identifier,
      tsubst: Map[Identifier, Type],
      vsubst: Map[Identifier, Expr],
      targsExtra: Seq[TypeParameter], // Extra type parameters to be passed through
      vargsExtra: Seq[Variable], // Extra value parameters to be passed through
      specialized: Set[Identifier], // Original parameters that are being specialized and thus be dropped
      pinned: Set[Identifier], // Original parameters that must not vary on recursive calls
    ) extends s.ConcreteStainlessSelfTreeTransformer {

      override def transform(expr: self.s.Expr): self.t.Expr = expr match {
        case v: Variable =>
          vsubst.getOrElse(v.id, super.transform(v))

        case fi: FunctionInvocation if fi.id == origFd.id =>
          val tpairs = origFd.tparams zip fi.tps
          val vpairs = origFd.params zip fi.args

          val changingParams =
            tpairs.collect { case (tparam, targ) if tparam.tp != targ => tparam.tp.id } ++
            vpairs.collect { case (param, arg) if param.toVariable != arg => param.id }
          val badParams = changingParams.toSet intersect pinned
          if (badParams.nonEmpty) {
            val badParamsStr = badParams.map(_.toString).mkString(", ")
            context.reporter.fatalError(fi.getPos,
              s"The parameters {$badParamsStr} of a specialized function are pinned, but vary in " +
              "this recursive call. Parameters get pinned when they are specialized or when " +
              s"they are part of specialization arguments.\n$helperMsg")
            return super.transform(fi)
          }

          val targs1 = tpairs.collect { case (tparam, targ) if !specialized(tparam.tp.id) => targ }
          val vargs1 = vpairs.collect { case (param, arg) if !specialized(param.id) => arg }
          val fi1 = FunctionInvocation(newId, tps = targs1 ++ targsExtra, args = vargs1 ++ vargsExtra)
          super.transform(fi1.copiedFrom(fi))

        case _ => super.transform(expr)
      }

      override def transform(tpe: self.s.Type): self.t.Type = tpe match {
        case tp: TypeParameter =>
          tsubst.getOrElse(tp.id, super.transform(tp))

        case _ => super.transform(tpe)
      }
    }

    def isIndirectlyRecursive(id: Identifier): Boolean =
      (callGraph.succ(id) - id) exists {
        succId => callGraph.transitiveSucc(succId) contains id
      }

    def mergeOptions[S <: Specification](s1: Option[S], s2: Option[S])(f: (S, S) => S): Option[S] =
      (s1, s2) match {
        case (None, None) => None
        case (Some(_), None) => s1
        case (None, Some(_)) => s2
        case (Some(s1), Some(s2)) => Some(f(s1, s2))
      }

    // Unpack the outer function `fd`

    val speccedOuter = BodyWithSpecs(fd.fullBody)

    if (speccedOuter.specs.exists(_.kind == LetKind)) {
      check(fd.fullBody)
      return Some(fd)
    }

    // Detect whether the outer function is specializing another function `origFd`

    val (origFd, specializer) = speccedOuter.body match {
      case specFi @ SpecializeCall(fi) =>
        if (isIndirectlyRecursive(fi.id)) {
          context.reporter.fatalError(fi.getPos,
            "Cannot use `specialize` on function with indirect recursion.")
          return None
        }

        val origFd = fi.tfd.fd
        val tpairs = origFd.tparams zip fi.tps
        val vpairs = origFd.params zip fi.args

        val tsubst = tpairs.map { case (tparam, targ) => tparam.tp.id -> targ } .toMap
        val vsubst = vpairs.map { case (param, arg) => param.id -> arg } .toMap

        var tparamsOuter = fd.tparams
        var paramsOuter = fd.params

        var tspecialized = Set.empty[Identifier] // specialized type parameters
        var vspecialized = Set.empty[Identifier] // specialized value parameters
        var newPinnedInArgs = Set.empty[Identifier] // new parameters referred to in spec. args
        var newToOrig = Map.empty[Identifier, Identifier] // mapping of new to original parameters

        // Match tparams and params one-by-one.
        // FIXME: Rule out any complex expressions as `targs` and `vargs`?
        tpairs.foreach { case (tparam, targ) =>
          tparamsOuter match {
            case tparamOuter +: rest if tparamOuter.tp == targ =>
              newToOrig += tparamOuter.tp.id -> tparam.tp.id
              tparamsOuter = rest
            case _ =>
              tspecialized += tparam.tp.id
              newPinnedInArgs ++= typeOps.typeParamsOf(targ).map(_.id)
              newPinnedInArgs ++= typeOps.variablesOf(targ).map(_.id)
          }
        }
        vpairs.foreach { case (param, arg) =>
          paramsOuter match {
            case paramOuter +: rest if paramOuter.toVariable == arg =>
              newToOrig += paramOuter.id -> param.id
              paramsOuter = rest
            case _ =>
              vspecialized += param.id
              newPinnedInArgs ++= typeOps.typeParamsOf(arg).map(_.id)
              newPinnedInArgs ++= exprOps.variablesOf(arg).map(_.id)
          }
        }

        // Left-over `tparamsOuter` and `paramsOuter` become extra pass-through arguments.
        newPinnedInArgs = newPinnedInArgs -- tparamsOuter.map(_.tp.id) -- paramsOuter.map(_.id)

        val specialized = tspecialized ++ vspecialized
        val pinned = newPinnedInArgs.map(newToOrig) ++ specialized

        if (context.reporter.isDebugEnabled) {
          val specArgsStr =
            tspecialized.map(id => s"$id:=${tsubst(id).asString}").mkString(", ") + "; " +
            vspecialized.map(id => s"$id:=${vsubst(id).asString}").mkString(", ")
          val pinnedStr = pinned.map(_.toString).mkString(", ")
          context.reporter.debug(fi.getPos,
            s"Specializing ${origFd.id} with arguments $specArgsStr (pinning {$pinnedStr})")
        }

        val specializer = new Specializer(
          origFd, fd.id,
          tsubst, vsubst,
          tparamsOuter.map(_.tp), paramsOuter.map(_.toVariable),
          specialized, pinned
        )
        (origFd, specializer)

      case _ =>
        check(fd.fullBody)
        return Some(fd)
    }

    val fullBodySpecialized = specializer.transform(origFd.fullBody)

    // Conjoin pre- and postconditions of the original and the specialized function
    val specced1 = BodyWithSpecs(fullBodySpecialized)
    val specced2 = specced1.copy(
      specs = Seq(
        mergeOptions(specced1.getSpec(PostconditionKind), speccedOuter.getSpec(PostconditionKind)) {
          case (
            Postcondition(Lambda(Seq(res1), cond1)),
            pc2 @ Postcondition(lam2 @ Lambda(Seq(res2), cond2))
          ) =>
            val cond = and(cond1, exprOps.replaceFromSymbols(Map(res2 -> res1.toVariable), cond2))
            Postcondition(Lambda(Seq(res1), cond.copiedFrom(cond2)).copiedFrom(lam2))
              .setPos(pc2.getPos)
        },
        mergeOptions(specced1.getSpec(PreconditionKind), speccedOuter.getSpec(PreconditionKind)) {
          case (Precondition(cond1), pc2 @ Precondition(cond2)) =>
            Precondition(and(cond1, cond2).copiedFrom(cond2))
              .setPos(pc2.getPos)
        },
        specced1.getSpec(MeasureKind),
      ).flatten
    )

    val fullBody1 = specced2.reconstructed
    val fullBody2 = exprOps.freshenLocals(fullBody1)
    val fullBody3 = symbols.simplifyExpr(fullBody2)(using inox.solvers.PurityOptions(context))

    check(fullBody3)

    Some(fd.copy(
      fullBody = fullBody3
    ).copiedFrom(fd))
  }
}

object FunctionSpecialization {
  def apply(trees: Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends FunctionSpecialization(s)(t)
    new Impl(trees, trees)
  }
}
