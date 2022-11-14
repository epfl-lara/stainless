/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import stainless.extraction.utils

import scala.collection.mutable

class OpaqueChooseInjector private(val trees: ast.Trees)
                                  (override val s: trees.type,
                                   override val t: trees.type)
                                  (using inox.Context)
  extends inox.transformers.SymbolTransformer {

  def this(trees: ast.Trees)(using inox.Context) = this(trees)(trees, trees)

  import trees._
  import exprOps._

  private case class Injector(symbols: Symbols) extends stainless.transformers.TreeTransformer {
    override final val s: trees.type = trees
    override final val t: trees.type = trees

    override def transform(fd: FunDef): FunDef = {
      if (fd.flags.contains(Extern) || fd.flags.contains(Opaque)) {
        val specced = BodyWithSpecs(fd.fullBody)
        val post = specced.getSpec(PostconditionKind)
        val choose = post
          .map {
            case Postcondition(Lambda(Seq(vd), post)) =>
              Choose(vd, freshenLocals(specced.wrapLets(post)))
            case Postcondition(l@Lambda(_, _)) =>
              sys.error(s"Unexpected number of params for postcondition lambda: $l")
          }
          .getOrElse {
            Choose(ValDef(FreshIdentifier("res", true), fd.returnType), BooleanLiteral(true))
          }
          .copiedFrom(fd)
        fd.copy(fullBody = specced.copy(body = choose).reconstructed)
      } else fd
    }
  }

  override def transform(symbols: Symbols): Symbols = {
    val inj = Injector(symbols)
    val syms1 = t.NoSymbols
      .withSorts(symbols.sorts.values.toSeq)
      .withFunctions(symbols.functions.values.toSeq.map(inj.transform))
    val chooseEnc = extraction.inlining.ChooseEncoder(s, t)
    chooseEnc.extract(syms1)._1
  }
}

object OpaqueChooseInjector {
  def apply(p: Program)(using inox.Context): inox.transformers.SymbolTransformer {
    val s: p.trees.type
    val t: p.trees.type
  } = {
    class Impl(override val trees: p.trees.type) extends OpaqueChooseInjector(trees)
    new Impl(p.trees)
  }
}
