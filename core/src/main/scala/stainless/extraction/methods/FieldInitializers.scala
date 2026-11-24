/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package extraction
package methods

import stainless.ast.{Symbol, SymbolIdentifier}

/** Makes the initialisers of the fields of abstract classes verified.
  *
  * The initialiser of a field runs for all the instances of the subclasses of its class, including
  * those that override the field. `MethodLifting` however only keeps the bodies that the dispatch
  * of the accessors may reach, and `FieldAccessors` inlines these, so the verification conditions
  * of such an initialiser would otherwise not be generated:
  *
  * {{{
  * abstract class Shape {
  *   val sides: BigInt = { assert(false); BigInt(3) } // runs when a `Square` is created
  * }
  * case class Square(override val sides: BigInt) extends Shape
  * }}}
  *
  * This phase adds, for each such field, a final method of the class with the same body, which is
  * verified in place of the initialiser.
  */
trait FieldInitializers extends ExtractionPipeline {
  val s: Trees
  val t: s.type
  import s._

  override def invalidate(id: Identifier): Unit = ()

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    val initializers = symbols.functions.values.toSeq.sortBy(_.getPos).flatMap { fd =>
      val cdOpt = fd.flags.collectFirst { case IsMethodOf(cid) => symbols.getClass(cid) }
      (fd.id, cdOpt) match {
        case (id: SymbolIdentifier, Some(cd))
        if cd.isAbstract && fd.isField(isLazy = false) && fd.hasBody && !fd.isExtern && !fd.isSynthetic =>
          val last = s"${cd.id.name}$$${id.symbol.path.last}$$init"
          val newId = SymbolIdentifier(Symbol((id.symbol.path.init :+ last).mkString(".")))
          val kept = fd.flags.filter(f => f == Ghost || f.name == "pure")
          Some(exprOps.freshenSignature(new FunDef(
            newId, fd.tparams, fd.params, fd.returnType, fd.fullBody,
            kept ++ Seq(IsMethodOf(cd.id), Final, Synthetic, Derived(Some(fd.id)))
          ).copiedFrom(fd)))
        case _ => None
      }
    }

    if (initializers.isEmpty) (symbols, ExtractionSummary.NoSummary)
    else (symbols.withFunctions(initializers), ExtractionSummary.NoSummary)
  }
}

object FieldInitializers {
  def apply(tr: Trees)(using inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = {
    class Impl(override val s: tr.type, override val t: tr.type)
              (using override val context: inox.Context) extends FieldInitializers
    new Impl(tr, tr)
  }
}
