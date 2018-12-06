package stainless.frontends.fast.elaboration

import inox.parser.ElaborationErrors
import inox.parser.elaboration.SimpleTypes
import stainless.frontends.fast.IRs

trait Constraints extends inox.parser.elaboration.Constraints { self: IRs with SimpleTypes with ElaborationErrors =>

  import SimpleTypes._
  import StainlessConstraints._

  object StainlessConstraints {
    case class OneOf(options: Seq[Type], tpe: Type) extends Constraint
  }

  object StainlessConstraint {
    def oneOf(options: Seq[Type], tpe: Type): Constraint = OneOf(options, tpe)
  }

}
