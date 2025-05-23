/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.Await
import scala.concurrent.duration._
import extraction.xlang.{ TreeSanitizer, trees => xt }

class FullImperativeSuite extends VerificationComponentTestSuite with inox.MainHelpers {

  override def configurations = super.configurations.map {
    seq => Seq(
      extraction.imperative.optFullImperative(true),
      inox.optTimeout(75)
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // FIXME(gsps): Incomplete
    case "full-imperative/valid/CellDataStructuresAndRepr" => Skip
    // FIXME(gsps): Time-out?
    case "full-imperative/invalid/OpaqueEffectsGeneric" => Skip

    // FIXME(gsps): Works, but slow
    case "full-imperative/valid/TreeImmutMap" => Skip
    // FIXME(gsps): Works, but flaky on CI?
    case "full-imperative/valid/TreeImmutMapGeneric" => Skip

    // Timeout on z3-4.12.2
    case "full-imperative/valid/StackSimple" => Skip

    case _ => super.filter(ctx, name)
  }

  // We filter out the 'copy' method from the extracted symbols,
  // since it involves allocations, and that isn't supported yet.
  // TODO: when allocation is supported, remove the identifierFilter
  import FullImperativeSuite._

  testPosAll("full-imperative/valid", valid, identifierFilter = i => !i.name.startsWith("copy"))

  testNegAll("full-imperative/invalid", invalid, identifierFilter = i => !i.name.startsWith("copy"))
}
object FullImperativeSuite {
  private lazy val valid = ComponentTestSuite.loadPrograms("full-imperative/valid")
  private lazy val invalid = ComponentTestSuite.loadPrograms("full-imperative/invalid")
}