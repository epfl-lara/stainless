/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package transformers

import scala.language.existentials
import scala.concurrent.duration._

trait SimplifierWithSolver extends inox.transformers.SimplifierWithPC { self =>
  import trees._
  import symbols._

  implicit val context: inox.Context

  protected val semantics: inox.SemanticsProvider {
    val trees: self.trees.type
  }

  protected val program: inox.Program {
    val trees: self.trees.type
    val symbols: self.symbols.type
  } = inox.Program(trees)(symbols)

  protected val solver =
    semantics.getSemantics(program)
      .getSolver(context)
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
  }

  implicit object Env extends PathProvider[Env] {
    override val empty = new Env(Path.empty)
    override def apply(path: Path) = new Env(path)
  }

  override def initEnv = Env.empty
}

