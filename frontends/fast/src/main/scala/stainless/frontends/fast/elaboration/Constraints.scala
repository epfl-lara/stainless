package stainless.frontends.fast.elaboration

import inox.parser.ElaborationErrors
import inox.parser.elaboration.SimpleTypes
import stainless.frontends.fast.IRs

trait Constraints extends inox.parser.elaboration.Constraints { self: IRs with SimpleTypes with ElaborationErrors =>

  import SimpleTypes._
  import StainlessConstraints._

  object StainlessConstraints {
    case class OneOf(tpe: Type, constraintGenerator: Type => Seq[Constraint]) extends Constraint
  }

  object StainlessConstraint {
    def oneOf(tpe: Type, constraintGenerator: Type => Seq[Constraint]): Constraint =
      OneOf(tpe, constraintGenerator)
  }

  override implicit lazy val constraintUnifiable: Unifiable[Constraint] = Unifiable {
    case Constraints.Exists(elem) => for {
      e <- Eventual.unify(elem)
    } yield Constraints.Exists(e)
    case Constraints.Equals(left, right) => for {
      l <- Eventual.unify(left)
      r <- Eventual.unify(right)
    } yield Constraints.Equals(l, r)
    case Constraints.HasClass(elem, typeClass) => for {
      e <- Eventual.unify(elem)
      t <- Eventual.unify(typeClass)
    } yield Constraints.HasClass(e, t)
    case OneOf(tpe, constraintGenerator) =>
      for {
      t <- Eventual.unify(tpe)
    } yield StainlessConstraints.OneOf(t, constraintGenerator)
  }

}
