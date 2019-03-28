/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent._

import org.scalatest._
import org.scalatest.concurrent._

import scala.concurrent.{ Await, Future }
import scala.concurrent.duration._

class TypeCheckerInternalSuite extends FunSuite with Matchers with TimeLimits { self =>

  import stainless.trees._

  val maxId = ast.SymbolIdentifier("max")
  val maxX = ValDef.fresh("x", IntegerType())
  val maxY = ValDef.fresh("y", IntegerType())
  val maxFd = new FunDef(
    maxId,
    Seq(),
    Seq(maxX, maxY),
    IntegerType(),
    IfExpr(GreaterEquals(maxX.toVariable, maxY.toVariable), maxX.toVariable, maxY.toVariable),
    Seq()
  )
  def max(x: Expr, y: Expr) = FunctionInvocation(maxId, Seq(), Seq(x,y))

  val checkId = ast.SymbolIdentifier("check")
  val checkCond = ValDef.fresh("cond", BooleanType())
  val checkFd = new FunDef(
    checkId,
    Seq(),
    Seq(checkCond),
    UnitType(),
    Ensuring(
      Require(
        checkCond.toVariable,
        UnitLiteral()
      ),
      Lambda(
        Seq(ValDef.fresh("u", UnitType())),
        checkCond.toVariable
      )
    ),
    Seq()
  )
  def check(cond: Expr, rest: Expr) =
    Let(
      ValDef.fresh("u", RefinementType(ValDef.fresh("u", UnitType()), cond)),
      FunctionInvocation(checkId, Seq(), Seq(cond)),
      rest
    )

  val streamId = ast.SymbolIdentifier("Stream")
  val constantId = ast.SymbolIdentifier("constant")
  val streamConsId = ast.SymbolIdentifier("SCons")
  val tp = TypeParameter.fresh("T")
  val tpDef = TypeParameterDef(tp)
  val vdHead = ValDef(FreshIdentifier("head"), tp)
  val vdTail = ValDef(FreshIdentifier("tail"), FunctionType(Seq(), ADTType(streamId, Seq(tp))))
  val streamCons = new ADTConstructor(streamConsId, streamId, Seq(vdHead, vdTail))
  val streamSort = new ADTSort(streamId, Seq(tpDef), Seq(streamCons), Seq())

  def scons(tpe: Type, head: Expr, tail: Expr, index: Expr): Expr =
    SizedADT(streamCons.id, Seq(tpe), Seq(head, Lambda(Seq(), tail)), index)

  def scons(tpe: Type, head: Expr, tail: Expr): Expr =
    ADT(streamCons.id, Seq(tpe), Seq(head, Lambda(Seq(), tail)))

  def head(s: Expr): Expr = ADTSelector(s, vdHead.id)
  def head(vd: ValDef): Expr = head(vd.toVariable)

  def tail(s: Expr): Expr = Application(ADTSelector(s, vdTail.id), Seq())
  def tail(vd: ValDef): Expr = tail(vd.toVariable)

  val constantTp = TypeParameter.fresh("T")
  val constantN = ValDef(FreshIdentifier("n"), IntegerType())
  val constantArg = ValDef(FreshIdentifier("t"), constantTp)
  val constantCode =
    scons(
      constantTp,
      constantArg.toVariable,
      FunctionInvocation(constantId, Seq(constantTp), Seq(
        Minus(constantN.toVariable, IntegerLiteral(1)),
        constantArg.toVariable
      )),
      constantN.toVariable
    )
  val constantBody =
    Require(
      GreaterEquals(constantN.toVariable, IntegerLiteral(0)),
      Decreases(
        constantN.toVariable,
        constantCode
      )
    )
  val constantFd = new FunDef(
    constantId,
    Seq(TypeParameterDef(constantTp)),
    Seq(constantN, constantArg),
    RecursiveType(streamId, Seq(constantTp), constantN.toVariable),
    constantBody,
    Seq()
  )

  val zipWithId = ast.SymbolIdentifier("zipWith")
  val tpX = TypeParameter.fresh("X")
  val tpXDef = TypeParameterDef(tpX)
  val tpY = TypeParameter.fresh("Y")
  val tpYDef = TypeParameterDef(tpY)
  val tpZ = TypeParameter.fresh("Z")
  val tpZDef = TypeParameterDef(tpZ)

  val zipN = ValDef(FreshIdentifier("n"), IntegerType())
  val zipFun = ValDef(FreshIdentifier("f"), FunctionType(Seq(tpX, tpY), tpZ))
  val zipS1 = ValDef(FreshIdentifier("s1"), RecursiveType(streamId, Seq(tpX), zipN.toVariable))
  val zipS2 = ValDef(FreshIdentifier("s2"), RecursiveType(streamId, Seq(tpY), zipN.toVariable))

  val zipCode =
    scons(
      tpZ,
      Application(zipFun.toVariable, Seq(head(zipS1), head(zipS2))),
      FunctionInvocation(zipWithId, Seq(tpX, tpY, tpZ), Seq(
        Minus(zipN.toVariable, IntegerLiteral(1)),
        zipFun.toVariable,
        tail(zipS1),
        tail(zipS2)
      )),
      zipN.toVariable
    )
  val zipBody =
    Require(
      GreaterEquals(zipN.toVariable, IntegerLiteral(0)),
      Decreases(
        zipN.toVariable,
        zipCode
      )
    )

  val zipWithFd = new FunDef(
    zipWithId,
    Seq(tpXDef, tpYDef, tpZDef),
    Seq(zipN, zipFun, zipS1, zipS2),
    RecursiveType(streamId, Seq(tpZ), zipN.toVariable),
    zipBody,
    Seq()
  )

  val adderParam1 = ValDef.fresh("a", IntegerType())
  val adderParam2 = ValDef.fresh("b", IntegerType())
  val adder = Lambda(Seq(adderParam1, adderParam2),
    Plus(adderParam1.toVariable, adderParam2.toVariable))

  val fibId = ast.SymbolIdentifier("fib")
  val fibN = ValDef.fresh("n", IntegerType())
  val fibCode =
    scons(
      IntegerType(),
      IntegerLiteral(0),
      scons(
        IntegerType(),
        IntegerLiteral(1),
        FunctionInvocation(zipWithId, Seq(IntegerType(),IntegerType(),IntegerType()), Seq(
          Minus(fibN.toVariable, IntegerLiteral(2)),
          adder,
          FunctionInvocation(fibId, Seq(), Seq(Minus(fibN.toVariable, IntegerLiteral(2)))),
          tail(FunctionInvocation(fibId, Seq(), Seq(Minus(fibN.toVariable, IntegerLiteral(1))))),
        )),
        Minus(fibN.toVariable, IntegerLiteral(1))
      ),
      fibN.toVariable
    )
  val fibBody =
    Require(
      GreaterEquals(fibN.toVariable, IntegerLiteral(0)),
      Decreases(
        fibN.toVariable,
        fibCode
      )
    )

  val fibFd = new FunDef(
    fibId,
    Seq(),
    Seq(fibN),
    RecursiveType(streamId, Seq(IntegerType()), fibN.toVariable),
    fibBody,
    Seq()
  )

  // Example is inspired from "A Unifying Approach to Recursive and Co-recursive Definitions"
  // Replace contiguous sequences of ones by digits between 1 and 9
  val compressId = ast.SymbolIdentifier("compress")
  val compressN = ValDef.fresh("n", IntegerType())
  val compressS = ValDef.fresh("s", ADTType(streamId, Seq(IntegerType())))

  val compressSHead1 = ValDef.fresh("h1", IntegerType())
  val compressSHead2 = ValDef.fresh("h2", IntegerType())
  val compressCode =
    Let(
      compressSHead1,
      head(compressS),
      Let(
        compressSHead2,
        head(tail(compressS)),
        IfExpr(
          and(
            GreaterEquals(compressSHead1.toVariable, IntegerLiteral(1)),
            LessThan(compressSHead1.toVariable, IntegerLiteral(9)),
            Equals(compressSHead2.toVariable, IntegerLiteral(1))
          ),
          FunctionInvocation(
            compressId,
            Seq(),
            Seq(
              compressN.toVariable,
              scons(
                IntegerType(),
                Plus(compressSHead1.toVariable, IntegerLiteral(1)),
                tail(tail(compressS))
              )
            )
          ),
          scons(
            IntegerType(),
            compressSHead1.toVariable,
            FunctionInvocation(
              compressId,
              Seq(),
              Seq(
                Minus(compressN.toVariable, IntegerLiteral(1)),
                tail(compressS)
              )
            ),
            compressN.toVariable
          )
        )
      )
    )
  val compressBody =
    Require(
      GreaterEquals(compressN.toVariable, IntegerLiteral(0)),
      Decreases(
        Tuple(Seq(compressN.toVariable, max(Minus(IntegerLiteral(9), head(compressS)), IntegerLiteral(0)))),
        compressCode
      )
    )

  val compressFd = new FunDef(
    compressId,
    Seq(),
    Seq(compressN, compressS),
    RecursiveType(streamId, Seq(IntegerType()), compressN.toVariable),
    compressBody,
    Seq()
  )

  val takeId = ast.SymbolIdentifier("take")
  val takeN = ValDef.fresh("n", IntegerType())
  val takeTp = TypeParameter.fresh("T")
  val takeTpDef = TypeParameterDef(takeTp)
  val takeS = ValDef.fresh("s", RecursiveType(streamId, Seq(takeTp), takeN.toVariable))

  val takeCode =
    IfExpr(
      LessEquals(takeN.toVariable, IntegerLiteral(0)),
      head(takeS),
      FunctionInvocation(
        takeId, Seq(takeTp), Seq(
          Minus(takeN.toVariable, IntegerLiteral(1)),
          tail(takeS)
        )
      )
    )
  val takeBody =
    Require(
      GreaterEquals(takeN.toVariable, IntegerLiteral(0)),
      Decreases(
        takeN.toVariable,
        takeCode
      )
    )

  val takeFd = new FunDef(
    takeId,
    Seq(takeTpDef),
    Seq(takeN, takeS),
    takeTp,
    takeBody,
    Seq()
  )

  def greaterThanType(lowerBound: BigInt) = {
    val vd = ValDef.fresh("i", IntegerType())
    RefinementType(vd, GreaterThan(vd.toVariable, IntegerLiteral(lowerBound)))
  }

  val compressOnesId = ast.SymbolIdentifier("compressOnes")
  val compressOnesN = ValDef.fresh("n", IntegerType())
  val compressOnesS = ValDef.fresh("s", ADTType(streamId, Seq(IntegerType())))
  val compressOnesPiArg =
    ValDef.fresh("i", greaterThanType(0))
  val compressOnesP = ValDef.fresh("p",
    PiType(
      Seq(compressOnesPiArg),
      RefinementType(
        ValDef.fresh("u", UnitType()),
        Equals(
          FunctionInvocation(
            takeId,
            Seq(IntegerType()),
            Seq(compressOnesPiArg.toVariable, compressOnesS.toVariable)
          ),
          IntegerLiteral(1)
        )
      )
    ))


  val compressOnesSHead1 = ValDef.fresh("h1", IntegerType())
  val compressOnesSHead2 = ValDef.fresh("h2", IntegerType())
  val compressOnesCode =
    Let(
      compressOnesSHead1,
      head(compressOnesS),
      Let(
        compressOnesSHead2,
        head(tail(compressOnesS)),
        IfExpr(
          and(
            GreaterEquals(compressOnesSHead1.toVariable, IntegerLiteral(1)),
            LessThan(compressOnesSHead1.toVariable, IntegerLiteral(9)),
            Equals(compressOnesSHead2.toVariable, IntegerLiteral(1))
          ),
          FunctionInvocation(
            compressOnesId,
            Seq(),
            Seq(
              compressOnesN.toVariable,
              scons(IntegerType(), Plus(compressOnesSHead1.toVariable, IntegerLiteral(1)), tail(tail(compressOnesS))), {
                val vd = ValDef.fresh("i", greaterThanType(0))
                Lambda(
                  Seq(vd),
                  Let(
                    ValDef.fresh("p1",
                      RefinementType(
                        ValDef.fresh("u", UnitType()),
                        Equals(
                          FunctionInvocation(
                            takeId,
                            Seq(IntegerType()),
                            Seq(Plus(vd.toVariable, IntegerLiteral(1)), compressOnesS.toVariable)
                          ),
                          IntegerLiteral(1)
                        )
                      )
                    ),
                    Application(compressOnesP.toVariable, Seq(Plus(vd.toVariable, IntegerLiteral(1)))),
                    check(
                      Equals(
                        FunctionInvocation(
                          takeId,
                          Seq(IntegerType()),
                          Seq(Plus(vd.toVariable, IntegerLiteral(1)), compressOnesS.toVariable)
                        ),
                        IntegerLiteral(1)
                      ),
                      check(
                        Equals(
                          FunctionInvocation(
                            takeId,
                            Seq(IntegerType()),
                            Seq(vd.toVariable, tail(compressOnesS))
                          ),
                          IntegerLiteral(1)
                        ),
                        UnitLiteral()
                      )
                    )
                  )
                )
              }
            )
          ),
          Let(
            ValDef.fresh("p1",
              RefinementType(
                ValDef.fresh("u", UnitType()),
                Equals(
                  FunctionInvocation(
                    takeId,
                    Seq(IntegerType()),
                    Seq(IntegerLiteral(1), compressOnesS.toVariable)
                  ),
                  IntegerLiteral(1)
                )
              )
            ),
            Application(compressOnesP.toVariable, Seq(IntegerLiteral(1))),
            IfExpr(
              Equals(compressOnesN.toVariable, IntegerLiteral(0)),
              UnitLiteral(),
              FunctionInvocation(
                compressOnesId,
                Seq(),
                Seq(
                  Minus(compressOnesN.toVariable, IntegerLiteral(1)),
                  tail(compressOnesS), {
                    val vd = ValDef.fresh("i", greaterThanType(0))
                    Lambda(
                      Seq(vd),
                      Let(
                        ValDef.fresh("p1",
                          RefinementType(
                            ValDef.fresh("u", UnitType()),
                            Equals(
                              FunctionInvocation(
                                takeId,
                                Seq(IntegerType()),
                                Seq(Plus(vd.toVariable, IntegerLiteral(1)), compressOnesS.toVariable)
                              ),
                              IntegerLiteral(1)
                            )
                          )
                        ),
                        Application(compressOnesP.toVariable, Seq(Plus(vd.toVariable, IntegerLiteral(1)))),
                        check(
                          Equals(
                            FunctionInvocation(
                              takeId,
                              Seq(IntegerType()),
                              Seq(Plus(vd.toVariable, IntegerLiteral(1)), compressOnesS.toVariable)
                            ),
                            IntegerLiteral(1)
                          ),
                          check(
                            Equals(
                              FunctionInvocation(
                                takeId,
                                Seq(IntegerType()),
                                Seq(vd.toVariable, tail(compressOnesS))
                              ),
                              IntegerLiteral(1)
                            ),
                            UnitLiteral()
                          )
                        )
                      )
                    )
                  }
                )
              )
            )
          )
        )
      )
    )
  val compressOnesBody =
    Ensuring(
      Require(
        and(
          GreaterEquals(head(compressOnesS), IntegerLiteral(1)),
          LessEquals(head(compressOnesS), IntegerLiteral(9)),
          GreaterEquals(compressOnesN.toVariable, IntegerLiteral(0))
        ),
        Decreases(
          Tuple(Seq(compressOnesN.toVariable, max(Minus(IntegerLiteral(9), head(compressOnesS)), IntegerLiteral(0)))),
          compressOnesCode
        )
      ),
      Lambda(
        Seq(ValDef.fresh("u", UnitType())),
        Equals(
          FunctionInvocation(
            takeId,
            Seq(IntegerType()),
            Seq(
              compressOnesN.toVariable,
              FunctionInvocation(
                compressId,
                Seq(),
                Seq(compressOnesN.toVariable, compressOnesS.toVariable)
              )
            )
          ),
          IntegerLiteral(9)
        )
      )
    )
  val compressOnesFd = new FunDef(
    compressOnesId,
    Seq(),
    Seq(compressOnesN, compressOnesS, compressOnesP),
    UnitType(),
    compressOnesBody,
    Seq()
  )

  val funs = Seq(constantFd, zipWithFd, fibFd, compressFd, maxFd, takeFd, compressOnesFd, checkFd)
  val syms =
    NoSymbols.withFunctions(funs)
             .withSorts(Seq(streamSort))

  val program: StainlessProgram = new inox.Program {
    val trees: stainless.trees.type = stainless.trees
    val symbols = syms
  }

  val reporter = new inox.DefaultReporter(Set())
  implicit val ctx =
    inox.Context(
      reporter,
      new inox.utils.InterruptManager(reporter),
      inox.Options(
        Seq(
          verification.optVCCache(false),
          inox.optTimeout(10)
        )
      ),
    )
  import org.scalatest._

  // reporter.info(program.asString)

  test("Stream examples") {
    val vcs = TypeChecker.checkType(program, ctx)(funs.map(_.id))
    val future = VerificationChecker.verify(program, ctx)(vcs)
    implicit val ec = ExecutionContext.global
    val r = Await.result(future, Duration.Inf)
    val analysis =
      new VerificationAnalysis {
        override val program: self.program.type = self.program
        override val context = ctx
        override val sources = funs.map(_.id).toSet
        override val results = r
      }
    analysis.toReport.emit(ctx)
    reporter.info(program.asString)
    for ((vc, vcResult) <- r) {
      assert(vcResult.isValid)
    }
  }

}
