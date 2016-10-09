/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

import inox._
import inox.solvers.{Solver => _, _}

trait InoxSolver extends inox.solvers.Solver {
  val encoder: SolverEncoder { val trees: program.trees.type }
  val underlying: inox.solvers.Solver { val program: InoxProgram }

  lazy val name = underlying.name
  lazy val options = underlying.options

  import program._
  import program.trees._

  import SolverResponses._

  def assertCnstr(expr: Expr): Unit = {
    underlying.assertCnstr(encoder.encode(expr))
  }

  private def convert(config: Configuration)
                     (resp: config.Response[underlying.Model, underlying.Assumptions]):
                     config.Response[Model, Assumptions] = {
    config.convert(resp,
      (model: underlying.Model) => model.map(p => ValDef(p._1.id, encoder.decode(p._1.tpe)) -> encoder.decode(p._2)),
      (assumptions: underlying.Assumptions) => assumptions.map(e => encoder.decode(e))
    )
  }

  def check(config: CheckConfiguration): config.Response[Model, Assumptions] = {
    convert(config)(underlying.check(config))
  }

  def checkAssumptions(config: Configuration)(assumptions: Set[Expr]): config.Response[Model, Assumptions] = {
    convert(config)(underlying.checkAssumptions(config)(assumptions map encoder.encode))
  }

  def free(): Unit = underlying.free()
  def reset(): Unit = underlying.reset()
  def push(): Unit = underlying.push()
  def pop(): Unit = underlying.pop()
}

object InoxSolver {
  def apply(p: StainlessProgram): Solver { val program: p.type } = new {
    val encoder: SolverEncoder { val program: p.type } = SolverEncoder(p)
    val underlying: inox.solvers.Solver { val program: encoder.targetProgram.type } = encoder.targetProgram
  } with InoxSolver
}
