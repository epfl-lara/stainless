package stainless
package verification

import CoqExpression._

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

case class CoqTactic(id: CoqIdentifier, tactics: Seq[CoqExpression]) extends CoqCommand {
  override def coqString = s"Ltac ${id.coqString} := " + tactics.map (t => t.coqString).mkString("\n  || ") + "."
}

case class CoqMatchTactic(id: CoqIdentifier, cases: Seq[CoqCase]) extends CoqCommand {
  override def coqString = s"Ltac ${id.coqString} := match goal with\n" +
    cases.map(cs => "\t" + tabulate(cs.coqString) + "\n").mkString +
    "end.\n"
}

case class InductiveDefinition(id: CoqIdentifier, params: Seq[(CoqIdentifier,CoqExpression)], cases: Seq[InductiveCase]) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"(${arg.coqString}: ${ty.coqString}) " }.mkString
  override def coqString = {
    // println("Translating: " + id.coqString)
   s"Inductive ${id.coqString} ${paramString}:=" +
    cases.map(_.coqString).mkString("\n","\n",".\n")
  }
}

// case class FixpointDefinition(id: CoqIdentifier, params: Seq[(CoqIdentifier,CoqExpression)], returnType: CoqExpression, body: CoqExpression) extends CoqCommand {
//   val paramString = params.map { case (arg,ty) => s"(${arg.coqString}: ${ty.coqString}) " }.mkString
//   override def coqString = {
//     // println("Translating: " + id.coqString)
//     s"Program Fixpoint ${id.coqString} ${paramString} { measure ignore_termination }: ${returnType.coqString} :=\n" +
//       body.coqString + ".\n"
//   }
// }

case class NormalDefinition(id: CoqIdentifier, params: Seq[(CoqIdentifier,CoqExpression)], returnType: CoqExpression, body: CoqExpression) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"(${arg.coqString}: ${ty.coqString}) " }.mkString
  override def coqString = {
    // println("Translating: " + id.coqString)
    s"Definition ${id.coqString} ${paramString}: ${returnType.coqString} :=\n" +
      body.coqString + ".\n\nFail Next Obligation.\n"
  }
}

case class CoqEquation(id: CoqIdentifier, params: Seq[(CoqIdentifier, CoqExpression)], returnType: CoqExpression, cases: Seq[(CoqExpression, CoqExpression)], ignoreTermination: Boolean) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"(${arg.coqString}: ${ty.coqString})" }.mkString(" ")
  override def coqString = s"Equations (noind) ${id.coqString} $paramString : ${returnType.coqString}\n" +
    cases.map {case (cs, expr) =>
      if (ignoreTermination)
        s"  by wf ignore_termination lt :=\n" +
        s"  ${cs.coqString} := ${tabulate(expr.coqString)}"
      else
        s"\n${cs.coqString} := ${tabulate(expr.coqString)}"
    }.mkString("", ";\n", ".")
}

case class CoqLemma(name: CoqIdentifier, body: CoqExpression, proof: CoqCommand) extends CoqCommand {
  override def coqString =
      s"Lemma ${name.coqString}: ${body.coqString}.\n" +
      "Proof.\n" +
      s"\t${tabulate(proof.coqString)}" +
      s"\nQed.\n"

}

case class SeparatorComment(s: String) extends CoqCommand {
  override def coqString = "(***********************\n  " + s + "\n ***********************)\n"
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

  def ===(that: CoqExpression) = CoqEquals(this,that)

  def apply(es: CoqExpression*) = {
    CoqApplication(this, es.toSeq)
  }
}

case object TypeSort extends CoqExpression {
  override def coqString: String = "Type"
}

case object CoqBool extends CoqExpression {
  override def coqString: String = "bool"
}

case object CoqZ extends CoqExpression {
  override def coqString: String = "Z"
}

case class Arrow(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  def coqString: String = {
    optP(e1) + " -> " + optP(e2)
  }
}


case class BiArrow(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  def coqString: String = {
    optP(e1) + " <-> " + optP(e2)
  }
}

case class CoqMatch(matched: CoqExpression, cases: Seq[CoqCase]) extends CoqExpression {
  override def coqString =
    s"match ${matched.coqString} with" +
      cases.map(_.coqString).mkString("\n","\n","\nend")
}

case class CoqApplication(f: CoqExpression, args: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = optP(f) + args.map(arg => " " + optP(arg)).mkString
}

case class CoqIdentifier(id: Identifier) extends CoqExpression {
  override def equals(o: scala.Any): Boolean = o match {
      //TODO FIXME
    case that@CoqIdentifier(thatID) => id.equals(thatID) && coqString.equals(that.coqString)
    case _ => false
  }

  override def coqString = {
    val res = id.name.replaceAll("\\$","___")
      .replaceAll("::", "cons_")
      .replaceAll(":\\+", "snoc_")
      .replaceAll(":", "i_")
      .replaceAll("\\+", "plus_")
      .replaceAll("\\+\\+", "union_")
      .replaceAll("--", "substract_")
      .replaceAll("-", "minus_")
      .replaceAll("&", "c_")
    if (coqKeywords contains res) coqKeywords(res)
    else if (validCoqIdentifier(res)) res
    else throw new Exception(s"$res is not a valid coq identifier")
  }
}

case class CoqUnboundIdentifier(id: CoqIdentifier) extends  CoqExpression {
  override def coqString = {
    "?" + id.coqString
  }
}

case class CoqTuple(es: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = {
    es.map(_.coqString).mkString("(", ",", ")")
  }
}

case class CoqSequence(es: Seq[CoqExpression]) extends  CoqExpression {
  override def coqString = {
    val tmp = es.map(_.coqString).mkString(";")
    if (tmp.length > charsPerLine)
      tmp.replace(";", ";\n")
    else
      tmp
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
    /*propInBool.coqString + */"(" + args.foldLeft(body.coqString) { case (acc,(id,tpe)) =>
      s"forall ${id.coqString}: ${tpe.coqString}, $acc"
    } + ")"
}

case class CoqExists(args: Seq[(CoqIdentifier,CoqExpression)], body: CoqExpression) extends CoqExpression {
  override def coqString =
  /*propInBool.coqString + */"(" + args.foldLeft(body.coqString) { case (acc,(id,tpe)) =>
    s"exists ${id.coqString}: ${tpe.coqString}, $acc"
  } + ")"
}

case class CoqLet(vd: CoqIdentifier, tpe: Option[CoqExpression], value: CoqExpression, body: CoqExpression) extends CoqExpression {
  override def coqString = if (tpe.isDefined)
    s"let ${vd.coqString}: ${tpe.get.coqString} := (${value.coqString}) in (${body.coqString})"
  else
    s"let ${vd.coqString} := (${value.coqString}) in (${body.coqString})"
}

case class CoqLambda(vd: CoqIdentifier, body: CoqExpression) extends CoqExpression {
  override def coqString = s"fun ${vd.coqString} => ${body.coqString} "
}

// This class is used to represent the strings we want to print as is
case class RawExpression(s: String) extends CoqExpression {
  override def coqString = s
}

/**
 * Boolean operations and propositions
 */

case class IfThenElse(cond: CoqExpression, tpe: CoqExpression, tCond: CoqExpression, eCond: CoqExpression) extends CoqExpression {
  override def coqString = {
    val cString = optP(cond)
    val tpeString = optP(tpe)
    val tString = optP(tCond)
    val eString = optP(eCond)
    if (!cString.contains("\n"))
      s"ifthenelse $cString $tpeString\n\t${tabulate(tString)}\n\t${tabulate(eString)}"
    else
      s"ifthenelse\n\t${tabulate(cString)}\n\t${tabulate(tpeString)}\n\t${tabulate(tString)}\n\t${tabulate(eString)}"

  }
}


case class Orb(es: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = fold(falseBoolean, es) {
    case (a,b) => IfThenElse(a, CoqBool, CoqLambda(coqUnused, trueBoolean), CoqLambda(coqUnused,b))
  }.coqString
}

case class Andb(es: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = fold(trueBoolean, es) {
    case (a,b) => IfThenElse(a, CoqBool, CoqLambda(coqUnused , b), CoqLambda(coqUnused, falseBoolean))
  }.coqString
}

case class Negb(e: CoqExpression) extends CoqExpression {
  override def coqString = negbFun(e).coqString
}

case class CoqEquals(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = /*propInBool.coqString + */"(" + e1.coqString + " = " + e2.coqString + ")"
}

case class CoqZNum(i: BigInt) extends CoqExpression {
  override def coqString = s"($i)%Z"
}

/**
 * Greater or equals
 */

/*case class GreB(*e1: CoqExpression, e2:CoqExpression) {
  override def coqString =
}*/

case class CoqTupleType(ts: Seq[CoqExpression]) extends CoqExpression {
  override def coqString = ts.map(optP).mkString("(", " * ", ")%type")
}

/**
 * Set Operations
 */
case object CoqUnknown extends CoqExpression {
  override def coqString = "_"
}

case class CoqFiniteSet(args: Seq[CoqExpression], tpe: CoqExpression) extends CoqExpression {
  override def coqString = args.foldLeft[CoqExpression](CoqSetEmpty(tpe))(
    (acc, singl) => CoqSetUnion(acc, CoqSetSingleton(singl))
  ).coqString
}

case class CoqSetEmpty(tpe: CoqExpression) extends CoqExpression {
  override def coqString = s"@set_empty ${optP(tpe)}"
}

case class CoqSetSingleton(e: CoqExpression) extends CoqExpression {
  override def coqString = s"set_singleton ${optP(e)}"
}

case class CoqSetEquals(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = s"set_equality ${optP(e1)} ${optP(e2)}"
}

/*
* The problem is that we do not know which kind of set is this, and for the fst parameter it is required
*
**/
case class CoqSetUnion(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = s"set_union ${optP(e1)} ${optP(e2)}"
}

case class CoqSetIntersection(e1: CoqExpression, e2: CoqExpression) extends  CoqExpression {
  override def coqString = s"set_intersection ${optP(e1)} ${optP(e2)}"
}

case class CoqSetDifference(e1: CoqExpression, e2: CoqExpression) extends  CoqExpression {
  override def coqString = s"set_difference ${optP(e1)} ${optP(e2)}"
}

case class CoqSetSubset(e1: CoqExpression, e2: CoqExpression) extends  CoqExpression {
  override def coqString = s"set_subset ${optP(e1)} ${optP(e2)}"
}

case class CoqSetType(base: CoqExpression) extends CoqExpression {
  override def coqString = s"set (${base.coqString})"
}

case class CoqBelongs(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  override def coqString = s"set_elem_of ${optP(e1)} ${optP(e2)}"
}

// represents the refinement of the type `tpe` by `body`, i.e. {id: tpe | body}
case class Refinement(id: CoqIdentifier, tpe: CoqExpression, body: CoqExpression) extends CoqExpression {
  def coqString: String = {
    s"{${id.coqString}: ${tpe.coqString} | ${body.coqString}}"
  }
}

case class Rewrite(what: CoqExpression) extends CoqExpression {
  override def coqString = s"rewrite ${what.coqString} in *"
}

case class Mark(names: Seq[CoqExpression], label: String) extends CoqExpression {
  override def coqString = {
    val joinedString = names.map(exp => exp.coqString).mkString("(", ",", ")")
    "Mark " + joinedString + " \"" + label + "\""
  }
}

case class Marked(names: Seq[CoqExpression], label: String) extends CoqExpression {
  override def coqString = {
    val joinedString = names.map(exp => exp.coqString).mkString("(", ",", ")")
    "Marked " + joinedString + " \"" + label + "\""
  }
}

case class CoqContext(e: CoqExpression) extends CoqExpression {
  override def coqString = s"context[${e.coqString}]"
}

case class PoseProof(expr: CoqExpression, as :Option[CoqIdentifier] = None) extends CoqExpression {
  override def coqString: String = if (as.isEmpty) s"pose proof ${optP(expr)}" else s"pose proof ${optP(expr)} as ${as.get.coqString}"
}

case class CoqFresh(name: String) extends CoqExpression {
  override def coqString = "fresh \"" + name + "\""
}

// used in the CoqMatch construct
case class CoqCase(pattern: CoqPattern, body: CoqExpression) {
  def coqString: String = {
    val pString = pattern.coqString
    val bString = body.coqString
    if (bString.contains("\n") || bString.length + pString.length > charsPerLine) {
      s"| $pString =>\n\t\t${tabulate(bString,2)}"
    } else {
      s"| $pString => $bString"
    }

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


case class CoqTuplePatternVd(ps: Seq[CoqPattern], vd: VariablePattern) extends CoqPattern {
  override def coqString = {
    ps.map(_.coqString).mkString("(", ",", ")") + " as " + vd.coqString
  }
}

case class CoqTuplePattern(ps: Seq[CoqPattern]) extends CoqPattern {
  override def coqString = {
    ps.map(_.coqString).mkString("(", ",", ")")
  }
}

case class CoqTacticPattern(context: Map[CoqIdentifier,CoqExpression], goal: CoqExpression = CoqUnknown) extends CoqPattern {
  val contextString = context.map { case (id,e) => id.coqString + ": " + e.coqString }.mkString(", ")
  val goalString = goal.coqString
  override def coqString = s"[ $contextString |- $goalString ]"
}

object CoqExpression {
  def fold[T](baseCase: T, exprs: Seq[T])(operation: (T,T) => T) = {
    if (exprs.size == 0) baseCase
    else exprs.tail.foldLeft(exprs.head)(operation)
  }

  val implbFun = CoqLibraryConstant("implb")
  val andbFun = CoqLibraryConstant("andb")
  val orbFun = CoqLibraryConstant("orb")
  val negbFun = CoqLibraryConstant("negb")
  val trueProp = CoqLibraryConstant("True")
  val falseProp = CoqLibraryConstant("False")

  val trueBoolean = CoqLibraryConstant("true")
  val falseBoolean = CoqLibraryConstant("false")
  val propSort = CoqLibraryConstant("Prop")
  val propInBool = CoqLibraryConstant("propInBool")
  val magic = CoqLibraryConstant("magic")
  val typeSort = CoqLibraryConstant("Type")
  val mapType = CoqLibraryConstant("map_type")
  val ifthenelse = CoqLibraryConstant("ifthenelse")
  val CoqUnit = CoqLibraryConstant("unit")

  val fst = CoqLibraryConstant("fst")
  val snd = CoqLibraryConstant("snd")

  val applyLemma = CoqLibraryConstant("apply")
  val eq_sym = CoqLibraryConstant("eq_sym")
  val idtac = CoqLibraryConstant("idtac")

  val poseNew = CoqLibraryConstant("poseNew")

  val proj1 = CoqLibraryConstant("proj1")
  val proj1_sig = CoqLibraryConstant("proj1_sig")

  val coqUnused = CoqIdentifier(new Identifier("_", 0,0))

  val charsPerLine = 80

  def implb(e1: CoqExpression, e2: CoqExpression): CoqExpression = {
    CoqApplication(implbFun, Seq(e1,e2))
  }

  // we require too many parentheses!
  // we recompute coqString too many times
  def requiresParentheses(e: CoqExpression): Boolean = e.coqString.contains(" ")
  def requiresParentheses(e: CoqPattern): Boolean = e.coqString.contains(" ")

  def optP(e: CoqExpression) = if (requiresParentheses(e)) s"(${e.coqString})" else e.coqString
  def optP(e: CoqPattern) = if (requiresParentheses(e)) s"(${e.coqString})" else e.coqString

  def tabulate(s: String, n: Int = 1): String = {
    val tabs = ((1 to n).map(_ => "\t").mkString)
    s.replace("\n", "\n" + tabs)
  }

  def validCoqIdentifier(s: String) = s matches """[A-Z|a-z|_][\w_]*"""

  val coqKeywords = Map(
    "forall" -> "_forall",
    "exists" -> "_exists",
    "exists2" -> "_exists2"
  )

  // FIXME: not thread safe
  //var m: Map[String,String] = Map()
}
