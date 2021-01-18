/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package inlining

object DebugSectionFunctionSpecialization extends inox.DebugSection("fun-specialization")

trait FunctionSpecialization extends CachingPhase with IdentitySorts { self =>
  val s: Trees
  val t: s.type
  import s._

  implicit val debugSection = DebugSectionFunctionSpecialization

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult](
    (fd, symbols) => getDependencyKey(fd.id)(symbols)
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
    import symbols._

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

    class Specializer(
      origFd: FunDef,
      newId: Identifier,
      tsubst: Map[Identifier, Type],
      vsubst: Map[Identifier, Expr],
      targsExtra: Seq[TypeParameter], // Extra type parameters to be passed through
      vargsExtra: Seq[Variable], // Extra value parameters to be passed through
      specialized: Set[Identifier], // Original parameters that are being specialized and thus be dropped
      pinned: Set[Identifier], // Original parameters that must not vary on recursive calls
    ) extends s.SelfTreeTransformer {

      override def transform(expr: s.Expr): t.Expr = expr match {
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

      override def transform(tpe: s.Type): t.Type = tpe match {
        case tp: TypeParameter =>
          tsubst.getOrElse(tp.id, super.transform(tp))

        case _ => super.transform(tpe)
      }
    }

    def isIndirectlyRecursive(id: Identifier): Boolean =
      (callGraph.succ(id) - id) exists {
        succId => callGraph.transitiveSucc(succId) contains id
      }

    val (origFd, specializer) = fd.fullBody match {
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

        if (context.reporter.isDebugEnabled(debugSection)) {
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
        exprOps.preTraversal {
          case specFi @ SpecializeCall(_) =>
            context.reporter.fatalError(specFi.getPos,
              "The `specialize` construct must currently be used directly as the body of a " +
              "function without any contracts.")
          case fi: FunctionInvocation if fi.tfd.flags.contains(Template) =>
            context.reporter.fatalError(fi.getPos,
              "Cannot call an `@template` function directly, since it will be removed.")
          case _ =>
        }(fd.fullBody)
        return Some(fd)
    }

    val fullBody1 = exprOps.freshenLocals(specializer.transform(origFd.fullBody))
    val fullBody2 = symbols.simplifyExpr(fullBody1)(inox.solvers.PurityOptions(context))

    Some(fd.copy(
      fullBody = fullBody2,
      flags = (origFd.flags.filterNot(_ == Template) ++ fd.flags).distinct
    ).copiedFrom(fd))
  }
}

object FunctionSpecialization {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new FunctionSpecialization {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
