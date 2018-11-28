/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent._

import org.scalatest._
import org.scalatest.concurrent._

class TypeCheckerInternalSuite extends FunSuite with Matchers with TimeLimits { self =>

  import stainless.trees._

  val streamId = ast.SymbolIdentifier("Stream")
  val constantId = ast.SymbolIdentifier("constant")
  val streamConsId = ast.SymbolIdentifier("SCons")
  val tp = TypeParameter.fresh("T")
  val tpDef = TypeParameterDef(tp)
  val vdHead = ValDef(FreshIdentifier("head"), tp)
  val vdTail = ValDef(FreshIdentifier("tail"), FunctionType(Seq(), ADTType(streamId, Seq(tp))))
  val streamCons = new ADTConstructor(streamConsId, streamId, Seq(vdHead, vdTail))
  val streamSort = new ADTSort(streamId, Seq(tpDef), Seq(streamCons), Seq())

  val constantTp = TypeParameter.fresh("T")
  val constantN = ValDef(FreshIdentifier("n"), IntegerType())
  val constantArg = ValDef(FreshIdentifier("t"), constantTp)
  val constantCode =
    SizedADT(streamCons.id, Seq(constantTp),
      Seq(
        constantArg.toVariable,
        Lambda(Seq(),
          FunctionInvocation(constantId, Seq(constantTp), Seq(
            Minus(constantN.toVariable, IntegerLiteral(1)),
            constantArg.toVariable
          ))
        )
      ),
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
    SizedADT(streamCons.id, Seq(tpZ),
      Seq(
        Application(zipFun.toVariable, Seq(
          ADTSelector(zipS1.toVariable, vdHead.id),
          ADTSelector(zipS2.toVariable, vdHead.id)
        )),
        Lambda(Seq(),
          FunctionInvocation(zipWithId, Seq(tpX, tpY, tpZ), Seq(
            Minus(zipN.toVariable, IntegerLiteral(1)),
            zipFun.toVariable,
            Application(ADTSelector(zipS1.toVariable, vdTail.id), Seq()),
            Application(ADTSelector(zipS2.toVariable, vdTail.id), Seq())
          ))
        )
      ),
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
    SizedADT(streamCons.id, Seq(IntegerType()),
      Seq(IntegerLiteral(0), Lambda(Seq(),
        SizedADT(streamCons.id, Seq(IntegerType()),
          Seq(IntegerLiteral(1), Lambda(Seq(),
            FunctionInvocation(zipWithId, Seq(IntegerType(),IntegerType(),IntegerType()), Seq(
              Minus(fibN.toVariable, IntegerLiteral(2)),
              adder,
              FunctionInvocation(fibId, Seq(), Seq(Minus(fibN.toVariable, IntegerLiteral(2)))),
              Application(ADTSelector(
                FunctionInvocation(fibId, Seq(), Seq(Minus(fibN.toVariable, IntegerLiteral(1)))),
                vdTail.id
              ), Seq())
            ))
          )),
          Minus(fibN.toVariable, IntegerLiteral(1))
        ))
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

  val funs = Seq(constantFd, zipWithFd, fibFd)
  val syms =
    NoSymbols.withFunctions(funs)
             .withSorts(Seq(streamSort))

  val program: StainlessProgram = new inox.Program {
    val trees: stainless.trees.type = stainless.trees
    val symbols = syms
  }

  // println(program)

  implicit val ctx = inox.TestContext.empty
  import org.scalatest._

  test("Stream examples") {
    val vcs = TypeChecker.checkType(program, ctx)(funs.map(_.id))
    val future = VerificationChecker.verify(program, ctx)(vcs)
    implicit val ec = ExecutionContext.global
    future.onComplete { res =>
      for ((vc, vcResult) <- res.get) {
        assert(vcResult.isValid)
      }
    }
  }

}
