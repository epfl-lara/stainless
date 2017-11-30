package stainless
package verification

sealed abstract class CoqCommand {
  def coqString: String
}

case object NoCommand extends CoqCommand {
  override def coqString = ""
}
case class Sequence(e1: CoqCommand, e2: CoqCommand) extends CoqCommand {
  override def coqString = e1.coqString + "\n" + e2.coqString
}

case class InductiveDefinition(id: Identifier, params: Seq[(Identifier,CoqExpression)], cases: Seq[InductiveCase]) extends CoqCommand {
  val paramString = params.map { case (arg,ty) => s"($arg: $ty) " }.mkString
  override def coqString = 
   s"Inductive ${id.name} ${paramString}:=" +
   cases.map(_.coqString).mkString("\n","\n","\n.\n")
}

case class InductiveCase(constructor: Identifier, body: CoqExpression) {
  def coqString: String = {
    s"| ${constructor.name}: ${body.coqString}" 
  }
}

sealed abstract class CoqExpression {
  def coqString: String
}

case class Arrow(e1: CoqExpression, e2: CoqExpression) extends CoqExpression {
  def coqString: String = {
    e1.coqString + " -> " + e2.coqString
  }
}

case class ArbitraryExpression(s: String) extends CoqExpression {
  override def coqString = s
}
