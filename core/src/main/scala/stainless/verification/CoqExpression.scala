package stainless
package verification

import CoqExpression._

case class UnimplementedCoqOperation(msg: String) extends Exception(msg)

/**
 * Commands represent top-level Gallina declarations
 */
sealed abstract class CoqCommand {
  def coqString: String

  def $(c: CoqCommand) = Sequence(this,c)
}

case object NoCommand extends CoqCommand {
  override def coqString = ""
}

case class RequireImport(s: String) extends CoqCommand {
  override def coqString = s"Require Import $s."
}

case class Sequence(e1: CoqCommand, e2: CoqCommand) extends CoqCommand {
  override def coqString = e1.coqString + "\n" + e2.coqString
}

case class InductiveDefinition(id: Identifier, params: Seq[(Identifier,CoqExpression)], cases: Seq[InductiveCase]) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"($arg: $ty) " }.mkString
  override def coqString = 
   s"Inductive ${id.name} ${paramString}:=" +
    cases.map(_.coqString).mkString("\n","\n",".\n")
}

case class FixpointDefinition(id: Identifier, params: Seq[(Identifier,CoqExpression)], returnType: CoqExpression, body: CoqExpression) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"($arg: ${ty.coqString}) " }.mkString
  override def coqString = 
    s"Program Fixpoint ${id.name} ${paramString}:=\n" +
      body.coqString + ".\n"
}

case class NormalDefinition(id: Identifier, params: Seq[(Identifier,CoqExpression)], returnType: CoqExpression, body: CoqExpression) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"($arg: ${ty.coqString}) " }.mkString
  override def coqString = 
    s"Definition ${id.name} ${paramString}:=\n" +
      body.coqString + ".\n"
}

// This is used only for InductiveDefinition's
case class InductiveCase(constructor: Identifier, body: CoqExpression) {
  def coqString: String = {
    s"| ${constructor.name}: ${body.coqString}" 
  }
}


/**
  * Expressions describe Coq constructs for building terms/types/expressions
  */
sealed abstract class CoqExpression {
  def coqString: String
}

case object TypeSort extends CoqExpression {
  override def coqString: String = "Type"
}

case object CoqBool extends CoqExpression {
  override def coqString: String = "bool"
}

case class Arrow(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  def coqString: String = {
    e1.coqString + " -> " + e2.coqString
  }
}

case class CoqMatch(matched: CoqExpression, cases: Seq[CoqCase]) extends CoqExpression {
  override def coqString = 
   s"match ${matched.coqString} with" +
    cases.map(_.coqString).mkString("\n","\n","\nend\n")
}

case class CoqVariable(id: Identifier) extends CoqExpression {
  override def coqString = id.name
}

case class CoqApplication(f: CoqExpression, args: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = "(" + f.coqString + ")" + args.map(" (" + _.coqString + ")").mkString
}

case class CoqIdentifier(id: Identifier) extends CoqExpression {
  override def coqString = id.uniqueName
}

case class CoqLibraryFunction(s: String) extends CoqExpression {
  override def coqString = s
}

case class Constructor(id: CoqExpression, args: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = id.coqString + args.map(" (" + _.coqString + ")").mkString
}

case class CoqSelector(adt: CoqExpression, selector: CoqIdentifier) extends CoqExpression {
  override def coqString = CoqApplication(selector, Seq(adt)).coqString
}

case class CoqForall(args: Seq[(CoqIdentifier,CoqExpression)], body: CoqExpression) extends CoqExpression {
  override def coqString = 
    args.foldLeft(body.coqString) { case (acc,(id,tpe)) => 
      s"forall ${id.coqString}: ${tpe.coqString}, $acc"
    }
}

/**
 * Boolean operations and propositions
 */

case class Orb(es: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = fold(FalseBoolean.coqString, es.map(_.coqString)) { case (a,b) => s"$a || $b" }
}

case class Andb(es: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = fold(TrueBoolean.coqString, es.map(_.coqString)) { case (a,b) => s"$a && $b" }
}

case object TrueBoolean extends CoqExpression {
  override def coqString = "true"
}

case object FalseBoolean extends CoqExpression {
  override def coqString = "false"
}

case class CoqEquals(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = "(" + e1.coqString + ")" + " = " + "(" + e2.coqString + ")"
}



/**
 * Set Operations
 */
case class CoqFiniteSet(args: Seq[CoqExpression], tpe: CoqExpression) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqOperation("Finite Sets are not implemented yet.")
}

case class CoqSetUnion(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqOperation("Union of Sets are not implemented yet.")
}

case class CoqSetType(base: CoqExpression) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqOperation("The Set type is not implemented yet.")
}

case class CoqBelongs(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqOperation("Set membership- is not implemented yet.")
}

// represents the refinement of the type `tpe` by `body`, i.e. {id: tpe | body}
case class Refinement(id: CoqIdentifier, tpe: CoqExpression, body: CoqExpression) extends CoqExpression {
  def coqString: String = {
    s"{${id.coqString}: ${tpe.coqString} | ${body.coqString}}"
  }
}

// This class is used to represent the expressions for which we didn't make a construct
case class ArbitraryExpression(s: String) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqOperation(s)
}

// used in the CoqMatch construct
case class CoqCase(pattern: CoqPattern, body: CoqExpression) {
  def coqString: String = {
    s"| ${pattern.coqString} => ${body.coqString}" 
  }
}

/**
  * Patterns are used as the left-hand-side for match cases
  */
abstract class CoqPattern {
  def coqString: String
}

case class InductiveTypePattern(id: Identifier, subPatterns: Seq[CoqPattern]) extends CoqPattern {
  override def coqString = id + subPatterns.map(" (" + _.coqString + ")").mkString
}

case class VariablePattern(id: Option[Identifier]) extends CoqPattern {
  override def coqString = if (id.isEmpty) "_" else id.get.name
}

object CoqExpression {
  def fold[T](baseCase: T, exprs: Seq[T])(operation: (T,T) => T) = {
    if (exprs.size == 0) baseCase
    else exprs.tail.foldLeft(exprs.head)(operation)
  }

  val implbFun = CoqLibraryFunction("implb")
  val andbFun = CoqLibraryFunction("andb")
  val orbFun = CoqLibraryFunction("orb")

  def implb(e1: CoqExpression, e2: CoqExpression): CoqExpression = {
    CoqApplication(implbFun, Seq(e1,e2))
  }
}