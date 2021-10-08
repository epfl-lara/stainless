/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package transformers

import scala.concurrent.duration._

import inox.solvers.optCheckModels

trait SimplifierWithSolver extends inox.transformers.SimplifierWithPC { self =>
  import trees._
  import symbols.{given, _}
  import inox.solvers.factoryToTimeoutableFactory

  val context: inox.Context
  import context.given

  protected val semantics: inox.SemanticsProvider {
    val trees: self.trees.type
  }

  protected val program: inox.Program {
    val trees: self.trees.type
    val symbols: self.symbols.type
  } = inox.Program(trees)(symbols)

  protected lazy val solver =
    semantics.getSemantics(program)
      .getSolver(using context.withOpts(optCheckModels(false)))
      .withTimeout(150.millis)
      .toAPI
      .asInstanceOf[inox.solvers.SimpleSolverAPI {
        val program: self.program.type
      }]

  class Env private (val path: Path) extends PathLike[Env] with SolvingPath {
    override def implies(cond: Expr): Boolean = {
      if (cond.getType != BooleanType()) return false
      solver.solveVALID(path implies cond).getOrElse(false)
    }

    override def merge(that: Env): Env = new Env(path merge that.path)
    override def negate: Env = new Env(path.negate)
    override def withBinding(p: (ValDef, Expr)): Env = new Env(path withBinding p)
    override def withBound(b: ValDef): Env = new Env(path withBound b)
    override def withCond(e: Expr): Env = new Env(path withCond e)

    override def toString: String = path.toString

    override def in(that: inox.transformers.SimplifierWithPC {
      val trees: self.trees.type
      val symbols: self.symbols.type
    }) = that match {
      // The `& that.type` trick allows to convince Scala that `sp` and `that` are actually equal...
      case sp: (inox.transformers.SimplifierWithPath & that.type) =>
        path.elements.foldLeft(sp.initEnv) {
          case (spEnvAcc, Path.CloseBound(vd, v)) => spEnvAcc.withBinding((vd, v))
          case (spEnvAcc, Path.OpenBound(vd)) => spEnvAcc.withBound(vd)
          case (spEnvAcc, Path.Condition(e)) => spEnvAcc.withCond(e)
        }
      case _ => super.in(that)
    }
  }

  object Env extends PathProvider[Env] {
    override val empty = new Env(Path.empty)
    override def apply(path: Path) = new Env(path)
  }

  override def initEnv = Env.empty
}

