/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

object optIgnorePosts extends inox.FlagOptionDef("ignore-posts", false)

trait Strengthener { self: OrderingRelation =>
  val checker: ProcessingPipeline

  import checker._
  import checker.context._
  import checker.program._
  import checker.program.trees._
  import checker.program.symbols.{given, _}
  import CallGraphOrderings.{given, _}
  import exprOps._

  private val strengthenedPost: MutableMap[Identifier, Option[Lambda]] = MutableMap.empty

  def getPostconditions: MutableMap[Identifier, Lambda] =
    strengthenedPost.collect{ case (k,Some(v)) => k -> v }

  private lazy val ignorePosts = options.findOptionOrDefault(optIgnorePosts)

  private object postStrengthener extends ConcreteIdentitySymbolTransformer {
    override def transform(syms: Symbols): Symbols =
      syms.withFunctions(syms.functions.toSeq.map {
        case (id, fd) =>
          strengthenedPost.get(id) match {
            case Some(post @ Some(_)) => fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, post)).copiedFrom(fd)
            case _                    => fd
          }
      })
  }

  registerTransformer(postStrengthener)

  def strengthenPostconditions(funDefs: Set[FunDef])(using dbg: inox.DebugSection): Unit = {
    reporter.debug("- Strengthening postconditions")

    // Strengthen postconditions on all accessible functions by adding size constraints
    val callees: Set[FunDef] = funDefs.flatMap(fd => transitiveCallees(fd))
    val sortedCallees: Seq[FunDef] = callees.toSeq.sorted

    // Note that we don't try to add postconditions to the entire SCC as the case of
    // a stronger post existing for a single function within the SCC seems more probable
    // than having weird inter-dependencies between different functions in the SCC
    for (fd <- sortedCallees
         if fd.body.isDefined &&
           !strengthenedPost.isDefinedAt(fd.id) && checker
           .terminates(fd)
           .isGuaranteed) {

      strengthenedPost(fd.id) = None

      def strengthen(cmp: (Seq[Expr], Seq[Expr]) => Expr): Boolean = {
        val specced = BodyWithSpecs(fd.fullBody)

        val postcondition = {
          val res = ValDef.fresh("res", fd.returnType)
          val post = specced.getSpec(PostconditionKind) match {
            case Some(Postcondition(lambda)) if !ignorePosts  => application(lambda, Seq(res.toVariable))
            case _                                            => BooleanLiteral(true)
          }
          val sizePost = cmp(Seq(res.toVariable), fd.params.map(_.toVariable))
          Lambda(Seq(res), and(post, sizePost))
        }

        val letsAndRequires = specced.letsAndSpecs(PreconditionKind)
        val formula = letsAndRequires.foldRight(application(postcondition, Seq(specced.body))) {
          case (spec @ LetInSpec(vd, e), acc) => Let(vd, e, acc).setPos(spec)
          case (spec @ Precondition(pred), acc) => implies(pred, acc).setPos(spec)
          case _ => sys.error("shouldn't happen thanks to the filtering above")
        }

        val strengthener = new ConcreteIdentitySymbolTransformer {
          override def transform(syms: Symbols): Symbols = super.transform(syms).withFunctions {
            Seq(fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, Some(postcondition))).copiedFrom(fd))
          }
        }

        val api = getAPI(strengthener)

        // @nv: one must also check that variablesOf(formula) is non-empty as
        //      we may proceed to invalid strenghtening otherwise

        if (exprOps.variablesOf(formula).nonEmpty &&
            api.solveVALID(formula).contains(true)) {
          strengthenedPost(fd.id) = Some(postcondition)
          true
        } else {
          false
        }
      }

      // test if size is smaller or equal to input
      val weakConstraintHolds = strengthen(self.lessEquals)

      val strongConstraintHolds = if (weakConstraintHolds) {
        // try to improve postcondition with strictly smaller
        strengthen(self.lessThan)
      } else {
        false
      }

      //if (weakConstraintHolds || strongConstraintHolds) clearSolvers()

    }
  }

  sealed abstract class SizeConstraint
  case object StrongDecreasing extends SizeConstraint
  case object WeakDecreasing extends SizeConstraint
  case object NoConstraint extends SizeConstraint

  private val strengthenedApp: MutableSet[FunDef] = MutableSet.empty

  protected def strengthened(fd: FunDef): Boolean = strengthenedApp(fd)

  private val appConstraint: MutableMap[(Identifier, Identifier), SizeConstraint] = MutableMap.empty

  def applicationConstraint(fid: Identifier, id: Identifier, largs: Seq[ValDef], args: Seq[Expr]): Expr =
    appConstraint.get(fid -> id) match {
      case Some(StrongDecreasing) => self.lessThan(largs.map(_.toVariable), args)
      case Some(WeakDecreasing)   => self.lessEquals(largs.map(_.toVariable), args)
      case _                      => BooleanLiteral(true)
    }

  def strengthenApplications(funDefs: Set[FunDef])(using dbg: inox.DebugSection): Unit = {
    reporter.debug("- Strengthening applications")

    val api = getAPI

    val transitiveFunDefs = funDefs ++ funDefs.flatMap(transitiveCallees)
    val sortedFunDefs = transitiveFunDefs.toSeq.sorted

    for (fd <- sortedFunDefs if fd.body.isDefined && !strengthenedApp(fd) && checker.terminates(fd).isGuaranteed) {

      val applications = collectWithPC(fd.fullBody) {
        case (Application(v: Variable, args), path) => (path, v, args)
      }.distinct

      val fdArgs = fd.params.map(_.toVariable)

      val allFormulas = for ((path, v, appArgs) <- applications) yield {
        val soft = path implies self.lessEquals(appArgs, fdArgs)
        val hard = path implies self.lessThan(appArgs, fdArgs)
        v -> ((soft, hard))
      }

      val formulaMap = allFormulas.groupBy(_._1).view.mapValues(_.map(_._2).unzip).toMap

      val constraints = for ((v, (weakFormulas, strongFormulas)) <- formulaMap) yield v -> {
        if (api.solveVALID(andJoin(weakFormulas.toSeq)).contains(true)) {
          if (api.solveVALID(andJoin(strongFormulas.toSeq)).contains(true)) {
            StrongDecreasing
          } else {
            WeakDecreasing
          }
        } else {
          NoConstraint
        }
      }

      val fdHOArgs = fdArgs.filter(_.tpe.isInstanceOf[FunctionType]).toSet

      val invocations = collectWithPC(fd.fullBody) {
        case (fi @ FunctionInvocation(_, _, args), path)
            if (fdHOArgs intersect args.collect { case v: Variable => v }.toSet).nonEmpty =>
          (path, args, (args zip fi.tfd.fd.params).collect {
            case (v: Variable, vd) if fdHOArgs(v) => v -> ((fi.id, vd.id))
          })
      }

      val var2invocations: Seq[(Variable, ((Identifier, Identifier), Path, Seq[Expr]))] =
        for ((path, args, mapping) <- invocations; (v, p) <- mapping) yield v -> (p, path, args)
      val invocationMap: Map[Variable, Seq[((Identifier, Identifier), Path, Seq[Expr])]] =
        var2invocations.groupBy(_._1).view.mapValues(_.map(_._2)).toMap

      def constraint(
          v: Variable,
          passings: Seq[((Identifier, Identifier), Path, Seq[Expr])]
      ): SizeConstraint = {
        if (constraints.get(v) == Some(NoConstraint)) NoConstraint
        else if (passings.exists(p => appConstraint.get(p._1) == Some(NoConstraint))) NoConstraint
        else
          passings.foldLeft[SizeConstraint](constraints.getOrElse(v, StrongDecreasing)) {
            case (constraint, (key, path, args)) =>
              lazy val strongFormula = path implies self.lessThan(args, fdArgs)
              lazy val weakFormula = path implies self.lessEquals(args, fdArgs)

              (constraint, appConstraint.get(key)) match {
                case (_, Some(NoConstraint)) => scala.sys.error("Whaaaat!?!? This shouldn't happen...")
                case (_, None)               => NoConstraint
                case (NoConstraint, _)       => NoConstraint
                case (StrongDecreasing | WeakDecreasing, Some(StrongDecreasing)) =>
                  if (api.solveVALID(weakFormula).contains(true)) StrongDecreasing
                  else NoConstraint
                case (StrongDecreasing, Some(WeakDecreasing)) =>
                  if (api.solveVALID(strongFormula).contains(true)) StrongDecreasing
                  else if (api.solveVALID(weakFormula).contains(true)) WeakDecreasing
                  else NoConstraint
                case (WeakDecreasing, Some(WeakDecreasing)) =>
                  if (api.solveVALID(weakFormula).contains(true)) WeakDecreasing
                  else NoConstraint
              }
          }
      }

      val outers = invocationMap.view.mapValues(_.filter(_._1._1 != fd)).toMap
      for (v <- fdHOArgs) {
        appConstraint(fd.id -> v.id) = constraint(v, outers.getOrElse(v, Seq.empty))
      }

      val selfs = invocationMap.view.mapValues(_.filter(_._1._1 == fd)).toMap
      for (v <- fdHOArgs) {
        appConstraint(fd.id -> v.id) = constraint(v, selfs.getOrElse(v, Seq.empty))
      }

      strengthenedApp += fd
    }
  }
}
