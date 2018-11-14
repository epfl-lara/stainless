package stainless.frontends.fast

import stainless.ast.SymbolIdentifier

trait Elaborators extends inox.parser.Elaborators with IRs {

  import Identifiers._

  class StainlessDefIdE extends super.DefIdE {
    override def elaborate(template: Identifier)(implicit store: Store): Constrained[(inox.Identifier, Option[String])] = template match {
      case IdentifierHole(index) => store.getHole[inox.Identifier](index) match {
        case None => Constrained.fail(invalidHoleType("Identifier")(template.pos))
        case Some(id) => Constrained.pure((id, None))
      }
      case IdentifierName(name) => Constrained.pure((SymbolIdentifier(name), Some(name)))
    }
  }
  override val DefIdE = new StainlessDefIdE
}
