/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Path
import purescala.Expressions._
import purescala.Types._
import purescala.ExprOps._
import purescala.Common._
import purescala.Definitions._
import purescala.Constructors._

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait Strengthener { self : RelationComparator =>

  val checker: TerminationChecker

  private val strengthenedPost : MutableSet[FunDef] = MutableSet.empty

  def strengthenPostconditions(funDefs: Set[FunDef])(implicit solver: Processor with Solvable) {
    // Strengthen postconditions on all accessible functions by adding size constraints
    val callees : Set[FunDef] = funDefs.flatMap(fd => checker.program.callGraph.transitiveCallees(fd))
    val sortedCallees : Seq[FunDef] = callees.toSeq.sortWith((fd1, fd2) => checker.program.callGraph.transitivelyCalls(fd2, fd1))

    for (funDef <- sortedCallees if !strengthenedPost(funDef) && funDef.hasBody && checker.terminates(funDef).isGuaranteed) {
      def strengthen(cmp: (Seq[Expr], Seq[Expr]) => Expr): Boolean = {
        val old = funDef.postcondition
        val postcondition = {
          val res = FreshIdentifier("res", funDef.returnType, true)
          val post = old.map{application(_, Seq(Variable(res)))}.getOrElse(BooleanLiteral(true))
          val sizePost = cmp(funDef.params.map(_.toVariable), Seq(res.toVariable))
          Lambda(Seq(ValDef(res)), and(post, sizePost))
        }

        funDef.postcondition = Some(postcondition)

        val prec = matchToIfThenElse(funDef.precOrTrue)
        val body = matchToIfThenElse(funDef.body.get)
        val post = matchToIfThenElse(postcondition)
        val formula = implies(prec, application(post, Seq(body)))

        // @nv: one must also check satisfiability here as if both formula and
        //      !formula are UNSAT, we will proceed to invalid strenghtening
        if (!solver.maybeSAT(formula) || !solver.definitiveALL(formula)) {
          funDef.postcondition = old
          false
        } else {
          true
        }
      }

      // test if size is smaller or equal to input
      val weekConstraintHolds = strengthen(self.softDecreasing)

      if (weekConstraintHolds) {
        // try to improve postcondition with strictly smaller
        strengthen(self.sizeDecreasing)
      }

      strengthenedPost += funDef
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
      case Some(StrongDecreasing) => self.sizeDecreasing(args, fargs.map(_.toVariable))
      case Some(WeakDecreasing) => self.softDecreasing(args, fargs.map(_.toVariable))
      case _ => BooleanLiteral(true)
    }
    case _ => BooleanLiteral(true)
  }

  def strengthenApplications(funDefs: Set[FunDef])(implicit solver: Processor with Solvable) {
    val transitiveFunDefs = funDefs ++ funDefs.flatMap(checker.program.callGraph.transitiveCallees)
    val sortedFunDefs = transitiveFunDefs.toSeq.sortWith((fd1, fd2) => checker.program.callGraph.transitivelyCalls(fd2, fd1))

    for (funDef <- sortedFunDefs if !strengthenedApp(funDef) && funDef.hasBody && checker.terminates(funDef).isGuaranteed) {

      val appCollector = new CollectorWithPaths[(Identifier,Path,Seq[Expr])] {
        def collect(e: Expr, path: Path): Option[(Identifier, Path, Seq[Expr])] = e match {
          case Application(Variable(id), args) => Some((id, path, args))
          case _ => None
        }
      }

      val applications = appCollector.traverse(funDef).distinct

      val funDefArgs = funDef.params.map(_.toVariable)

      val allFormulas = for ((id, path, appArgs) <- applications) yield {
        val soft = path implies self.softDecreasing(funDefArgs, appArgs)
        val hard = path implies self.sizeDecreasing(funDefArgs, appArgs)
        id -> ((soft, hard))
      }

      val formulaMap = allFormulas.groupBy(_._1).mapValues(_.map(_._2).unzip)

      val constraints = for ((id, (weakFormulas, strongFormulas)) <- formulaMap) yield id -> {
        if (solver.definitiveALL(andJoin(weakFormulas.toSeq))) {
          if (solver.definitiveALL(andJoin(strongFormulas.toSeq))) {
            StrongDecreasing
          } else {
            WeakDecreasing
          }
        } else {
          NoConstraint
        }
      }

      val funDefHOArgs = funDef.params.map(_.id).filter(_.getType.isInstanceOf[FunctionType]).toSet

      val fiCollector = new CollectorWithPaths[(Path, Seq[Expr], Seq[(Identifier,(FunDef, Identifier))])] {
        def collect(e: Expr, path: Path): Option[(Path, Seq[Expr], Seq[(Identifier,(FunDef, Identifier))])] = e match {
          case FunctionInvocation(tfd, args) if (funDefHOArgs intersect args.collect({ case Variable(id) => id }).toSet).nonEmpty =>
            Some((path, args, (args zip tfd.fd.params).collect {
              case (Variable(id), vd) if funDefHOArgs(id) => id -> ((tfd.fd, vd.id))
            }))
          case _ => None
        }
      }

      val invocations = fiCollector.traverse(funDef)
      val id2invocations : Seq[(Identifier, ((FunDef, Identifier), Path, Seq[Expr]))] =
        for {
          p <- invocations
          c <- p._3
        } yield c._1 -> (c._2, p._1, p._2)
      val invocationMap: Map[Identifier, Seq[((FunDef, Identifier), Path, Seq[Expr])]] =
        id2invocations.groupBy(_._1).mapValues(_.map(_._2))

      def constraint(id: Identifier, passings: Seq[((FunDef, Identifier), Path, Seq[Expr])]): SizeConstraint = {
        if (constraints.get(id) == Some(NoConstraint)) NoConstraint
        else if (passings.exists(p => appConstraint.get(p._1) == Some(NoConstraint))) NoConstraint
        else passings.foldLeft[SizeConstraint](constraints.getOrElse(id, StrongDecreasing)) {
          case (constraint, (key, path, args)) =>

            lazy val strongFormula = path implies self.sizeDecreasing(funDefArgs, args)
            lazy val weakFormula = path implies self.softDecreasing(funDefArgs, args)

            (constraint, appConstraint.get(key)) match {
              case (_, Some(NoConstraint)) => scala.sys.error("Whaaaat!?!? This shouldn't happen...")
              case (_, None) => NoConstraint
              case (NoConstraint, _) => NoConstraint
              case (StrongDecreasing | WeakDecreasing, Some(StrongDecreasing)) =>
                if (solver.definitiveALL(weakFormula)) StrongDecreasing
                else NoConstraint
              case (StrongDecreasing, Some(WeakDecreasing)) =>
                if (solver.definitiveALL(strongFormula)) StrongDecreasing
                else if (solver.definitiveALL(weakFormula)) WeakDecreasing
                else NoConstraint
              case (WeakDecreasing, Some(WeakDecreasing)) =>
                if (solver.definitiveALL(weakFormula)) WeakDecreasing
                else NoConstraint
            }
        }
      }

      val outers = invocationMap.mapValues(_.filter(_._1._1 != funDef))
      funDefHOArgs.foreach { id => appConstraint(funDef -> id) = constraint(id, outers.getOrElse(id, Seq.empty)) }

      val selfs = invocationMap.mapValues(_.filter(_._1._1 == funDef))
      funDefHOArgs.foreach { id => appConstraint(funDef -> id) = constraint(id, selfs.getOrElse(id, Seq.empty)) }

      strengthenedApp += funDef
    }
  }
}
