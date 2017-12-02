package stainless
package verification

import CoqExpression._

case class UnimplementedCoqExpression(msg: String) extends Exception(msg)

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

case class OpenScope(s: String) extends CoqCommand {
  override def coqString = s"Open Scope $s."
}

case class Sequence(e1: CoqCommand, e2: CoqCommand) extends CoqCommand {
  override def coqString = e1.coqString + "\n" + e2.coqString
}

case class InductiveDefinition(id: CoqIdentifier, params: Seq[(CoqIdentifier,CoqExpression)], cases: Seq[InductiveCase]) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"(${arg.coqString}: ${ty.coqString}) " }.mkString
  override def coqString = {
    // println("Translating: " + id.coqString)
   s"Inductive ${id.coqString} ${paramString}:=" +
    cases.map(_.coqString).mkString("\n","\n",".\n")
  }
}

case class FixpointDefinition(id: CoqIdentifier, params: Seq[(CoqIdentifier,CoqExpression)], returnType: CoqExpression, body: CoqExpression) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"(${arg.coqString}: ${ty.coqString}) " }.mkString
  override def coqString = try {
    // println("Translating: " + id.coqString)
    s"Program Fixpoint ${id.coqString} ${paramString}: ${returnType.coqString} :=\n" +
      body.coqString + ".\n"
  } catch {
    case UnimplementedCoqExpression(_) =>
      println(s"Warning: could not translate ${id.coqString} to Coq. Admitting definition for now.")
      s"Definition ${id.coqString} ${paramString}: ${returnType.coqString}. Admitted."
  }
}

case class NormalDefinition(id: CoqIdentifier, params: Seq[(CoqIdentifier,CoqExpression)], returnType: CoqExpression, body: CoqExpression) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"(${arg.coqString}: ${ty.coqString}) " }.mkString
  override def coqString = try {
    // println("Translating: " + id.coqString)
    s"Program Definition ${id.coqString} ${paramString}: ${returnType.coqString} :=\n" +
      body.coqString + ".\n"
  } catch {
    case UnimplementedCoqExpression(_) =>
      println(s"Warning: could not translate ${id.coqString} to Coq. Admitting definition for now.")
      s"Program Definition ${id.coqString} ${paramString}: ${returnType.coqString}. Admitted."
  }
}

// This class is used to represent the strings we want to print as is
case class RawCommand(s: String) extends CoqCommand {
  override def coqString = s
}

// This is used only for InductiveDefinition's
case class InductiveCase(constructor: CoqIdentifier, body: CoqExpression) {
  def coqString: String = {
    s"| ${constructor.coqString}: ${body.coqString}" 
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
    optP(e1) + " -> " + optP(e2)
  }
}

case class CoqMatch(matched: CoqExpression, cases: Seq[CoqCase]) extends CoqExpression {
  override def coqString = 
    s"match ${matched.coqString} with" +
      cases.map(_.coqString).mkString("\n","\n","\nend")
}

case class CoqVariable(id: Identifier) extends CoqExpression {
  override def coqString = id.name
}

case class CoqApplication(f: CoqExpression, args: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = optP(f) + args.map(arg => " " + optP(arg)).mkString
}

case class CoqIdentifier(id: Identifier) extends CoqExpression {
  override def coqString = {
    val res = id.name.replaceAll("\\$","___")
    if (validCoqIdentifier(res)) res
    else transformedName(res)
  }
}

case class CoqLibraryConstant(s: String) extends CoqExpression {
  override def coqString = s
}

case class Constructor(id: CoqExpression, args: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = id.coqString + args.map(arg => " " + optP(arg)).mkString
}

case class CoqForall(args: Seq[(CoqIdentifier,CoqExpression)], body: CoqExpression) extends CoqExpression {
  override def coqString = 
    propInBool.coqString + "(" + args.foldLeft(body.coqString) { case (acc,(id,tpe)) => 
      s"forall ${id.coqString}: ${tpe.coqString}, $acc"
    } + ")"
}

// This class is used to represent the strings we want to print as is
case class RawExpression(s: String) extends CoqExpression {
  override def coqString = s
}

/**
 * Boolean operations and propositions
 */

case class Orb(es: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = fold(FalseBoolean.coqString, es.map(_.coqString)) { case (a,b) => s"$a || $b" }
}

case class Andb(es: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = fold(TrueBoolean.coqString, es.map(_.coqString)) { case (a,b) => s"$a && $b" }
}

case object TrueBoolean extends CoqExpression {
  override def coqString = "true"
}

case object FalseBoolean extends CoqExpression {
  override def coqString = "false"
}

case class CoqEquals(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = propInBool.coqString + "(" + e1.coqString + " = " + e2.coqString + ")"
}



/**
 * Set Operations
 */
case class CoqFiniteSet(args: Seq[CoqExpression], tpe: CoqExpression) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqExpression("Finite Sets are not implemented yet.")
}

case class CoqSetUnion(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqExpression("Union of Sets are not implemented yet.")
}

case class CoqSetType(base: CoqExpression) extends CoqExpression {
  override def coqString = s"set (${base.coqString})"
}

case class CoqBelongs(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqExpression("Set membership is not implemented yet.")
}

// represents the refinement of the type `tpe` by `body`, i.e. {id: tpe | body}
case class Refinement(id: CoqIdentifier, tpe: CoqExpression, body: CoqExpression) extends CoqExpression {
  def coqString: String = try {
    s"{${id.coqString}: ${tpe.coqString} | ${body.coqString}}"
  } catch {
    case UnimplementedCoqExpression(_) =>
      println(s"IMPORTANT WARNING (Soundness): could not refine type $tpe by $body, due to unimplemented operations")
      tpe.coqString
  }
}

// This class is used to represent the expressions for which we didn't make a construct
case class UnimplementedExpression(s: String) extends CoqExpression {
  override def coqString = throw new UnimplementedCoqExpression(s)
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

case class InductiveTypePattern(id: CoqIdentifier, subPatterns: Seq[CoqPattern]) extends CoqPattern {
  override def coqString = id.coqString + subPatterns.map((p: CoqPattern) => 
    " " + optP(p)
  ).mkString
}

case class VariablePattern(id: Option[CoqIdentifier]) extends CoqPattern {
  override def coqString = if (id.isEmpty) "_" else id.get.coqString
}

object CoqExpression {
  def fold[T](baseCase: T, exprs: Seq[T])(operation: (T,T) => T) = {
    if (exprs.size == 0) baseCase
    else exprs.tail.foldLeft(exprs.head)(operation)
  }

  val implbFun = CoqLibraryConstant("implb")
  val andbFun = CoqLibraryConstant("andb")
  val orbFun = CoqLibraryConstant("orb")
  val trueProp = CoqLibraryConstant("True")
  val falseProp = CoqLibraryConstant("False")
  val propSort = CoqLibraryConstant("Prop")
  val propInBool = CoqLibraryConstant("propInBool")

  def implb(e1: CoqExpression, e2: CoqExpression): CoqExpression = {
    CoqApplication(implbFun, Seq(e1,e2))
  }

  // we require too many parentheses!
  // we recompute coqString too many times
  def requiresParentheses(e: CoqExpression): Boolean = e.coqString.contains(" ")
  def requiresParentheses(e: CoqPattern): Boolean = e.coqString.contains(" ")

  def optP(e: CoqExpression) = if (requiresParentheses(e)) s"(${e.coqString})" else e.coqString
  def optP(e: CoqPattern) = if (requiresParentheses(e)) s"(${e.coqString})" else e.coqString

  def validCoqIdentifier(s: String) = s matches """[\w_]+"""

  // FIXME: not thread safe
  var m: Map[String,String] = Map()

  // FIXME: not thread safe
  var i = 0
  def freshName() = {
    i += 1 // FIXME: not thread safe
    "ascii" + i
  }

  def transformedName(s: String) = {
    if (m.contains(s)) m(s)
    else {
      val v = freshName()
      println(s"transforming $s to $v")
      m += s -> v // FIXME: not thread safe
      v
    }
  }
}