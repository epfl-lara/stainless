/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package codegen.runtime

import utils._
import purescala.Expressions.{CaseClass => LeonCaseClass, _}
import purescala.Constructors._
import purescala.Definitions._
import purescala.Common._
import purescala.Types._
import purescala.TypeOps._
import purescala.ExprOps.{valuateWithModel, replaceFromIDs, variablesOf}
import purescala.Quantification.{extractQuorums, Domains}

import codegen.CompilationUnit

import scala.collection.immutable.{Map => ScalaMap}
import scala.collection.mutable.{HashMap => MutableMap, Set => MutableSet}
import scala.concurrent.duration._

import solvers.{SolverContext, SolverFactory}
import solvers.unrolling.UnrollingProcedure

import evaluators._
import synthesis._

abstract class Monitor {
  def onInvocation(): Unit

  def typeParams(params: Array[Int], tps: Array[Int], newTps: Array[Int]): Array[Int]

  def invariantCheck(obj: AnyRef, tpeIdx: Int): Boolean

  def invariantResult(obj: AnyRef, tpeIdx: Int, result: Boolean): Unit

  def onAbstractInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): AnyRef

  def onChooseInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): AnyRef

  def onForallInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): Boolean
}

class NoMonitor extends Monitor {
  def onInvocation(): Unit = {}

  def typeParams(params: Array[Int], tps: Array[Int], newTps: Array[Int]): Array[Int] = {
    throw new LeonCodeGenEvaluationException("No monitor available.")
  }

  def invariantCheck(obj: AnyRef, tpeIdx: Int): Boolean = {
    throw new LeonCodeGenEvaluationException("No monitor available.")
  }

  def invariantResult(obj: AnyRef, tpeIdx: Int, result: Boolean): Unit = {
    throw new LeonCodeGenEvaluationException("No monitor available.")
  }

  def onAbstractInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): AnyRef = {
    throw new LeonCodeGenEvaluationException("No monitor available.")
  }

  def onChooseInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): AnyRef = {
    throw new LeonCodeGenEvaluationException("No monitor available.")
  }

  def onForallInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): Boolean = {
    throw new LeonCodeGenEvaluationException("No monitor available.")
  }
}

class StdMonitor(unit: CompilationUnit, invocationsMax: Int, bodies: ScalaMap[Identifier, Expr], domains: Option[Domains] = None) extends Monitor {

  private[this] var invocations = 0

  def onInvocation(): Unit = {
    if (invocationsMax >= 0) {
      if (invocations < invocationsMax) {
        invocations += 1;
      } else {
        throw new LeonCodeGenEvaluationException("Maximum number of invocations reached ("+invocationsMax+").");
      }
    }
  }

  def invariantCheck(obj: AnyRef, tpeIdx: Int): Boolean = {
    val tpe = unit.runtimeIdToTypeMap(tpeIdx)
    val cc = unit.jvmToValue(obj, tpe).asInstanceOf[LeonCaseClass]
    val result = unit.bank.invariantCheck(cc)
    if (result.isFailure) throw new LeonCodeGenRuntimeException("ADT invariant failed @" + cc.ct.classDef.invariant.get.getPos)
    else result.isRequired
  }

  def invariantResult(obj: AnyRef, tpeIdx: Int, result: Boolean): Unit = {
    val tpe = unit.runtimeIdToTypeMap(tpeIdx)
    val cc = unit.jvmToValue(obj, tpe).asInstanceOf[LeonCaseClass]
    unit.bank.invariantResult(cc, result)
    if (!result) throw new LeonCodeGenRuntimeException("ADT invariant failed @" + cc.ct.classDef.invariant.get.getPos)
  }

  def typeParams(params: Array[Int], tps: Array[Int], newTps: Array[Int]): Array[Int] = {
    val tparams = params.toSeq.map(unit.runtimeIdToTypeMap(_).asInstanceOf[TypeParameter])
    val static = tps.toSeq.map(unit.runtimeIdToTypeMap(_))
    val newTypes = newTps.toSeq.map(unit.runtimeIdToTypeMap(_))
    val tpMap = (tparams zip newTypes).toMap
    static.map(tpe => unit.registerType(instantiateType(tpe, tpMap))).toArray
  }

  def onAbstractInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): AnyRef = {
    val fd = unit.runtimeAbstractMap(id)

    // TODO: extract types too!

    bodies.get(fd.id) match {
      case Some(expr) =>
        throw new LeonCodeGenRuntimeException("Found body!")

      case None =>
        throw new LeonCodeGenRuntimeException("Did not find body!")
    }
  }

  private[this] val chooseCache = new MutableMap[(Int, Seq[AnyRef]), AnyRef]()

  def onChooseInvocation(id: Int, tps: Array[Int], inputs: Array[AnyRef]): AnyRef = {
    implicit val debugSection = DebugSectionSynthesis

    val (tparams, p) = unit.runtimeProblemMap(id)

    val program = unit.program
    val ctx     = unit.ctx

    ctx.reporter.debug("Executing choose (codegen)!")
    val is = inputs.toSeq

    if (chooseCache contains ((id, is))) {
      chooseCache((id, is))
    } else {
      val tStart = System.currentTimeMillis

      val sctx = SolverContext(ctx, unit.bank)
      val solverf = SolverFactory.getFromSettings(sctx, program).withTimeout(10.second)
      val solver = solverf.getNewSolver()

      val newTypes = tps.toSeq.map(unit.runtimeIdToTypeMap(_))
      val tpMap = (tparams zip newTypes).toMap

      val newXs = p.xs.map { id =>
        val newTpe = instantiateType(id.getType, tpMap)
        if (id.getType == newTpe) id else FreshIdentifier(id.name, newTpe, true)
      }

      val newAs = p.as.map { id =>
        val newTpe = instantiateType(id.getType, tpMap)
        if (id.getType == newTpe) id else FreshIdentifier(id.name, newTpe, true)
      }

      val inputsMap = (newAs zip inputs).map {
        case (id, v) => id -> unit.jvmToValue(v, id.getType)
      }

      val instTpe: Expr => Expr = {
        val idMap = (p.as zip newAs).toMap ++ (p.xs zip newXs)
        instantiateType(_: Expr, tpMap, idMap)
      }

      val expr = p.pc map instTpe withBindings inputsMap and instTpe(p.phi)
      solver.assertCnstr(expr)

      try {
        solver.check match {
          case Some(true) =>
            val model = solver.getModel

            val valModel = valuateWithModel(model) _

            val res = newXs.map(valModel)
            val leonRes = tupleWrap(res) 

            val total = System.currentTimeMillis-tStart

            ctx.reporter.debug("Synthesis took "+total+"ms")
            ctx.reporter.debug("Finished synthesis with "+leonRes.asString(ctx))

            val obj = unit.valueToJVM(leonRes)(this)
            chooseCache += (id, is) -> obj
            obj
          case Some(false) =>
            throw new LeonCodeGenRuntimeException("Constraint is UNSAT")
          case _ =>
            throw new LeonCodeGenRuntimeException("Timeout exceeded")
        }
      } finally {
        solver.free()
        solverf.shutdown()
      }
    }
  }

  private[this] val forallCache = new MutableMap[(Int, Seq[AnyRef]), Boolean]()

  def onForallInvocation(id: Int, tps: Array[Int], args: Array[AnyRef]): Boolean = {
    implicit val debugSection = DebugSectionVerification

    val (tparams, f) = unit.runtimeForallMap(id)

    val program = unit.program

    val newOptions = Seq(
      LeonOption(UnrollingProcedure.optFeelingLucky)(false),
      LeonOption(UnrollingProcedure.optSilentErrors)(true),
      LeonOption(UnrollingProcedure.optCheckModels)(true)
    )

    val ctx = unit.ctx.copy(options = unit.ctx.options.filterNot { opt =>
      newOptions.exists(no => opt.optionDef == no.optionDef)
    } ++ newOptions)

    ctx.reporter.debug("Executing forall (codegen)!")
    val argsSeq = args.toSeq

    if (forallCache contains ((id, argsSeq))) {
      forallCache((id, argsSeq))
    } else {
      val tStart = System.currentTimeMillis

      val sctx = SolverContext(ctx, unit.bank)
      val solverf = SolverFactory.getFromSettings(sctx, program).withTimeout(.5.second)
      val solver = solverf.getNewSolver()

      val newTypes = tps.toSeq.map(unit.runtimeIdToTypeMap(_))
      val tpMap = (tparams zip newTypes).toMap

      val vars = variablesOf(f).toSeq.sortBy(_.uniqueName)
      val newVars = vars.map(id => FreshIdentifier(id.name, instantiateType(id.getType, tpMap), true))

      val Forall(fargs, body) = instantiateType(f, tpMap, (vars zip newVars).toMap)
      val mapping = (newVars zip argsSeq).map(p => p._1 -> unit.jvmToValue(p._2, p._1.getType)).toMap
      val cnstr = Not(replaceFromIDs(mapping, body))
      solver.assertCnstr(cnstr)

      if (domains.isDefined) {
        val dom = domains.get
        val quantifiers = fargs.map(_.id).toSet
        val quorums = extractQuorums(body, quantifiers)

        val domainCnstr = orJoin(quorums.map { quorum =>
          val quantifierDomains = quorum.flatMap { case (path, caller, args) =>
            val domain = caller match {
              case Variable(id) => dom.get(mapping(id))
              case _ => ctx.reporter.fatalError("Unexpected quantifier matcher: " + caller)
            }

            args.zipWithIndex.flatMap {
              case (Variable(id),idx) if quantifiers(id) =>
                Some(id -> domain.map(cargs => path -> cargs(idx)))
              case _ => None
            }
          }

          val domainMap = quantifierDomains.groupBy(_._1).mapValues(_.map(_._2).flatten)
          andJoin(domainMap.toSeq.map { case (id, dom) =>
            orJoin(dom.toSeq.map { case (path, value) =>
              // @nv: Note that we know id.getType is first-order since quantifiers can only
              //      range over basic types. This means equality is guaranteed well-defined
              //      between `id` and `value`
              path and Equals(Variable(id), value)
            })
          })
        })

        solver.assertCnstr(domainCnstr)
      }

      try {
        solver.check match {
          case Some(negRes) =>
            val res = !negRes
            val total = System.currentTimeMillis-tStart

            ctx.reporter.debug("Verification took "+total+"ms")
            ctx.reporter.debug("Finished forall evaluation with: "+res)

            forallCache += (id, argsSeq) -> res
            res

          case _ =>
            throw new LeonCodeGenRuntimeException("Timeout exceeded")
        }
      } finally {
        solver.free()
        solverf.shutdown()
      }
    }
  }
}

