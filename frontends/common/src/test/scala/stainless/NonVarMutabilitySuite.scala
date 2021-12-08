package stainless

import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers._
import extraction.xlang.{trees => xt}

class NonVarMutabilitySuite extends AnyFunSpec with InputUtils {

  val ctx: inox.Context = stainless.TestContext.empty
  import ctx.given

  describe("Mutation of a field that is not 'var' annotated") {
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

    it("should fail with not well formed exception") {
      val exception = the[xt.NotWellFormedException] thrownBy symbols.ensureWellFormed
      exception.getMessage should include(
        "cannot assign to immutable field 'field' of class 'ImmutableClass'"
      )
    }
  }
}
