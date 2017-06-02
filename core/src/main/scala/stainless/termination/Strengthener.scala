/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import transformers.CollectorWithPC
import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

object optIgnorePosts extends inox.FlagOptionDef("ignoreposts", false)

trait Strengthener { self: OrderingRelation =>

  val checker: ProcessingPipeline
  import checker._
  import program._
  import program.trees._
  import program.symbols._
  import CallGraphOrderings._

  private val strengthenedPost: MutableMap[FunDef, Option[Lambda]] = MutableMap.empty

  private lazy val ignorePosts = ctx.options.findOptionOrDefault(optIgnorePosts)

  private object postStrengthener extends IdentitySymbolTransformer {
    override def transform(syms: Symbols): Symbols =
      syms.withFunctions(strengthenedPost.flatMap {
        case (fd, post @ Some(_)) => Some(fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, post)))
        case _ => None
      }.toSeq)
  }

  registerTransformer(postStrengthener)

  def strengthenPostconditions(funDefs: Set[FunDef])(implicit dbg: inox.DebugSection): Unit = {
    ctx.reporter.debug("- Strengthening postconditions")

    // Strengthen postconditions on all accessible functions by adding size constraints
    val callees: Set[FunDef] = funDefs.flatMap(fd => transitiveCallees(fd))
    val sortedCallees: Seq[FunDef] = callees.toSeq.sorted

    // Note that we don't try to add postconditions to the entire SCC as the case of
    // a stronger post existing for a single function within the SCC seems more probable
    // than having weird inter-dependencies between different functions in the SCC
    for (fd <- sortedCallees
         if fd.body.isDefined && !strengthenedPost.isDefinedAt(fd) && checker.terminates(fd).isGuaranteed) {

      strengthenedPost(fd) = None

      def strengthen(cmp: (Seq[Expr], Seq[Expr]) => Expr): Boolean = {
        val postcondition = {
          val res = ValDef(FreshIdentifier("res"), fd.returnType, Set.empty)
          val post = fd.postcondition match {
            case Some(post) if !ignorePosts => application(post, Seq(res.toVariable))
            case _ => BooleanLiteral(true)
          }
          val sizePost = cmp(Seq(res.toVariable), fd.params.map(_.toVariable))
          Lambda(Seq(res), and(post, sizePost))
        }

        val formula = implies(fd.precOrTrue, application(postcondition, Seq(fd.body.get)))

        val strengthener = new IdentitySymbolTransformer {
          override def transform(syms: Symbols): Symbols = super.transform(syms).withFunctions {
            Seq(fd.copy(fullBody = exprOps.withPostcondition(fd.fullBody, Some(postcondition))))
          }
        }

        val api = getAPI(strengthener)

        // @nv: one must also check that variablesOf(formula) is non-empty as
        //      we may proceed to invalid strenghtening otherwise
        if (exprOps.variablesOf(formula).nonEmpty && api.solveVALID(formula).contains(true)) {
          strengthenedPost(fd) = Some(postcondition)
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

      if (weakConstraintHolds || strongConstraintHolds) clearSolvers()
    }
  }

  sealed abstract class SizeConstraint
  case object StrongDecreasing extends SizeConstraint
  case object WeakDecreasing extends SizeConstraint
  case object NoConstraint extends SizeConstraint

  private val strengthenedApp : MutableSet[FunDef] = MutableSet.empty

  protected def strengthened(fd: FunDef): Boolean = strengthenedApp(fd)

  private val appConstraint   : MutableMap[(FunDef, Identifier), SizeConstraint] = MutableMap.empty

  def applicationConstraint(fd: FunDef, id: Identifier, arg: Expr, args: Seq[Expr]): Expr = arg match {
    case Lambda(fargs, body) => appConstraint.get(fd -> id) match {
      case Some(StrongDecreasing) => self.lessThan(fargs.map(_.toVariable), args)
      case Some(WeakDecreasing) => self.lessEquals(fargs.map(_.toVariable), args)
      case _ => BooleanLiteral(true)
    }
    case _ => BooleanLiteral(true)
  }

  def strengthenApplications(funDefs: Set[FunDef])(implicit dbg: inox.DebugSection): Unit = {
    ctx.reporter.debug("- Strengthening applications")

    val api = getAPI

    val transitiveFunDefs = funDefs ++ funDefs.flatMap(transitiveCallees)
    val sortedFunDefs = transitiveFunDefs.toSeq.sorted

    for (fd <- sortedFunDefs if fd.body.isDefined && !strengthenedApp(fd) && checker.terminates(fd).isGuaranteed) {

      val appCollector = CollectorWithPC(program) {
        case (Application(v: Variable, args), path) => (path, v, args)
      }

      val applications = appCollector.collect(fd).distinct

      val fdArgs = fd.params.map(_.toVariable)

      val allFormulas = for ((path, v, appArgs) <- applications) yield {
        val soft = path implies self.lessEquals(appArgs, fdArgs)
        val hard = path implies self.lessThan(appArgs, fdArgs)
        v -> ((soft, hard))
      }

      val formulaMap = allFormulas.groupBy(_._1).mapValues(_.map(_._2).unzip)

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

      val fiCollector = CollectorWithPC(program) {
        case (fi @ FunctionInvocation(_, _, args), path)
        if (fdHOArgs intersect args.collect { case v: Variable => v }.toSet).nonEmpty =>
          val fd = fi.tfd.fd
          (path, args, (args zip fd.params).collect {
            case (v: Variable, vd) if fdHOArgs(v) => v -> ((fd, vd.id))
          })
      }

      val invocations = fiCollector.collect(fd)
      val var2invocations: Seq[(Variable, ((FunDef, Identifier), Path, Seq[Expr]))] =
        for ((path, args, mapping) <- invocations; (v, p) <- mapping) yield v -> (p, path, args)
      val invocationMap: Map[Variable, Seq[((FunDef, Identifier), Path, Seq[Expr])]] =
        var2invocations.groupBy(_._1).mapValues(_.map(_._2))

      def constraint(v: Variable, passings: Seq[((FunDef, Identifier), Path, Seq[Expr])]): SizeConstraint = {
        if (constraints.get(v) == Some(NoConstraint)) NoConstraint
        else if (passings.exists(p => appConstraint.get(p._1) == Some(NoConstraint))) NoConstraint
        else passings.foldLeft[SizeConstraint](constraints.getOrElse(v, StrongDecreasing)) {
          case (constraint, (key, path, args)) =>

            lazy val strongFormula = path implies self.lessThan(args, fdArgs)
            lazy val weakFormula = path implies self.lessEquals(args, fdArgs)

            (constraint, appConstraint.get(key)) match {
              case (_, Some(NoConstraint)) => scala.sys.error("Whaaaat!?!? This shouldn't happen...")
              case (_, None) => NoConstraint
              case (NoConstraint, _) => NoConstraint
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

      val outers = invocationMap.mapValues(_.filter(_._1._1 != fd))
      for (v <- fdHOArgs) appConstraint(fd -> v.id) = constraint(v, outers.getOrElse(v, Seq.empty))

      val selfs = invocationMap.mapValues(_.filter(_._1._1 == fd))
      for (v <- fdHOArgs) appConstraint(fd -> v.id) = constraint(v, selfs.getOrElse(v, Seq.empty))

      strengthenedApp += fd
    }
  }
}
