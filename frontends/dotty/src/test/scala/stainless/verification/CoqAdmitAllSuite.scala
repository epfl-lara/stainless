/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest.funsuite.AnyFunSuite
import stainless.trees.*

/** Checks how the Coq translation (`--coq`) discharges the obligations of a
 *  recursive function, with and without `--admit-all`. Coq itself is not run:
 *  the tests only inspect the generated file.
 */
class CoqAdmitAllSuite extends AnyFunSuite:

  private val sumId: Identifier = ast.SymbolIdentifier("sum")

  /** A recursive function with a contract:
   *  {{{
   *  def sum(n: BigInt): BigInt = {
   *    require(n >= 0)
   *    if (n == 0) 0 else n + sum(n - 1)
   *  }.ensuring(_ >= 0)
   *  }}}
   */
  private val sum: FunDef =
    val n = ValDef.fresh("n", IntegerType())
    val res = ValDef.fresh("res", IntegerType())
    val body = IfExpr(
      Equals(n.toVariable, IntegerLiteral(0)),
      IntegerLiteral(0),
      Plus(n.toVariable, FunctionInvocation(sumId, Seq(), Seq(Minus(n.toVariable, IntegerLiteral(1)))))
    )
    val fullBody = Ensuring(
      Require(GreaterEquals(n.toVariable, IntegerLiteral(0)), body),
      Lambda(Seq(res), GreaterEquals(res.toVariable, IntegerLiteral(0)))
    )
    new FunDef(sumId, Seq(), Seq(n), IntegerType(), fullBody, Seq())

  /** The Coq file that the translation generates to check `sum`, with the given
   *  options.
   */
  private def coqFileOfSum(options: inox.Options): String =
    val program = inox.Program(stainless.trees)(NoSymbols.withFunctions(Seq(sum)))
    val files = CoqEncoder.transformProgram(program, TestContext(options))
    files.collectFirst { case (`sumId`, _, command) => command.coqString }.get

  test("the obligations of a recursive function are solved by a tactic by default"):
    val file = coqFileOfSum(inox.Options.empty)
    assert(file.contains("Solve Obligations with"))
    assert(!file.contains("Admit Obligations."))

  test("--admit-all admits the obligations of a recursive function (#1850)"):
    val file = coqFileOfSum(inox.Options(Seq(optAdmitAll(true))))
    assert(file.contains("Admit Obligations."))
    assert(!file.contains("Solve Obligations with"))
