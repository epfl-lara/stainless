package leon
package termination

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Common._

import scala.collection.mutable.{Map => MutableMap}

final case class Relation(funDef: FunDef, path: Seq[Expr], call: FunctionInvocation) {
  override def toString : String = "Relation(" + funDef.id + "," + path + ", " + call.funDef.id + call.args.mkString("(",",",")") + ")"
}

class RelationBuilder {
  private val relationCache : MutableMap[FunDef, Set[Relation]] = MutableMap()

  def run(funDef: FunDef): Set[Relation] = relationCache.get(funDef) match {
    case Some(relations) => relations
    case None => {
      def visit(e: Expr, path: List[Expr]): Set[Relation] = e match {

        // we skip functions that aren't in this SCC since the call relations
        // associated to them don't interest us.
        case fi @ FunctionInvocation(f, args) =>
          val argRelations = args.flatMap(visit(_, path)).toSet
          argRelations + Relation(funDef, path.reverse.toSeq, fi)

        case Let(i, e, b) =>
          val ve = visit(e, path)
          val vb = visit(b, Equals(Variable(i), e) :: path)
          ve ++ vb

        case IfExpr(cond, thenn, elze) =>
          val vc = visit(cond, path)
          val vt = visit(thenn, cond :: path)
          val ve = visit(elze, Not(cond) :: path)
          vc ++ vt ++ ve

        case And(es) =>
          def resolveAnds(ands: List[Expr], p: List[Expr]): Set[Relation] = ands match {
            case x :: xs => visit(x, p ++ path) ++ resolveAnds(xs, x :: p)
            case Nil => Set()
          }
          resolveAnds(es.toList, Nil)

        case Or(es) =>
          def resolveOrs(ors: List[Expr], p: List[Expr]): Set[Relation] = ors match {
            case x :: xs => visit(x, p ++ path) ++ resolveOrs(xs, Not(x) :: p)
            case Nil => Set()
          }
          resolveOrs(es.toList, Nil)

        case UnaryOperator(e, _) => visit(e, path)

        case BinaryOperator(e1, e2, _) => visit(e1, path) ++ visit(e2, path)

        case NAryOperator(es, _) => es.map(visit(_, path)).flatten.toSet

        case t : Terminal => Set()

        case _ => sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
      }

      val precondition = funDef.precondition getOrElse BooleanLiteral(true)
      val precRelations = funDef.precondition.map(e => visit(simplifyLets(matchToIfThenElse(e)), Nil)) getOrElse Set()
      val bodyRelations = funDef.body.map(e => visit(simplifyLets(matchToIfThenElse(e)), List(precondition))) getOrElse Set()
      val postRelations = funDef.postcondition.map(e => visit(simplifyLets(matchToIfThenElse(e._2)), Nil)) getOrElse Set()
      val relations = precRelations ++ bodyRelations ++ postRelations
      relationCache(funDef) = relations
      relations
    }
  }
}
