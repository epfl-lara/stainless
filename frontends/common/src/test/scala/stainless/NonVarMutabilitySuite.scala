package stainless

import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers._

import extraction.xlang.{trees => xt}

class NonVarMutabilitySuite extends AnyFunSpec with InputUtils {

  implicit val ctx = stainless.TestContext.empty

  describe("Mutation of non-var annotated field") {
    val classId   = ast.SymbolIdentifier("ImmutableClass")
    val fieldId   = ast.SymbolIdentifier("field")
    val classType = xt.ClassType(classId, Seq())
    val param     = xt.ValDef(ast.SymbolIdentifier("var0"), classType, Seq())
    val varAlias  = xt.ValDef(ast.SymbolIdentifier("a"), classType, Seq(xt.IsVar))

    val classes = Seq(
      new xt.ClassDef(
        classId,
        Seq(),
        Seq(),
        Seq(xt.ValDef(fieldId, xt.BooleanType())),
        Seq(xt.IsSealed)
      )
    )
    val functions = Seq(
      new xt.FunDef(
        ast.SymbolIdentifier("setFalse"),
        Seq(),
        Seq(param),
        classType,
        xt.LetVar(
          varAlias,
          param.toVariable,
          xt.Block(
            Seq(xt.FieldAssignment(varAlias.toVariable, fieldId, xt.BooleanLiteral(false))),
            varAlias.toVariable
          )
        ),
        Seq()
      )
    )
    val symbols = xt.NoSymbols.withClasses(classes).withFunctions(functions)

    it("should fails") {
      the[Exception] thrownBy (
        extraction.pipeline.extract(symbols)
      ) should have message "Illegal aliasing: var0"
    }
  }
}
