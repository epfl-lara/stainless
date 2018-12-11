package stainless.frontends.fast.elaboration

import inox.parser.ElaborationErrors
import inox.parser.elaboration.SimpleTypes
import stainless.frontends.fast.IRs

trait Constraints extends inox.parser.elaboration.Constraints { self: IRs with SimpleTypes with ElaborationErrors =>

  import SimpleTypes._
  import StainlessConstraints._

  object StainlessConstraints {
    case class OneOf(tpe: Type, typeOptions: Seq[Type]) extends Constraint
    case class TypeOption(tpe: Type, option: Type) extends Constraint
  }

  object StainlessConstraint {
    def oneOf(tpe: Type, typeOptions: Seq[Type]): Constraint =
      OneOf(tpe, typeOptions)
    def option(tpe: Type, option: Type): Constraint =
      TypeOption(tpe, option)
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
    case OneOf(tpe, typeOptions) =>
      for {
      t <- Eventual.unify(tpe)
      goal <- Eventual.sequence(typeOptions.map(Eventual.unify(_)))
    } yield StainlessConstraints.OneOf(t, goal)
    case TypeOption(first, second) =>
      for {
        f <- Eventual.unify(first)
        s <- Eventual.unify(second)
      } yield StainlessConstraints.TypeOption(f, s)
  }
}
