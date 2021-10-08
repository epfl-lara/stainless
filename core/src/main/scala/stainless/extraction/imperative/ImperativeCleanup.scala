/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

/** Cleanup the program after running imperative desugaring.
  *
  * This functions simplifies away typical pattern of expressions
  * that can be generated during xlang desugaring phase. The most
  * common case is the generation of function returning tuple with
  * Unit in it, which can be safely eliminated.

  * We also eliminate expressions that deconstruct a tuple just to
  * reconstruct it right after.
  */
class ImperativeCleanup(override val s: Trees, override val t: oo.Trees)
                       (using override val context: inox.Context)
  extends oo.SimplePhase
     with SimplyCachedFunctions
     with SimplyCachedSorts
     with oo.SimplyCachedTypeDefs
     with oo.SimplyCachedClasses { self =>

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  protected class TransformerContext(override val s: self.s.type, override val t: self.t.type)
                                    (using val symbols: s.Symbols) extends oo.ConcreteTreeTransformer(s, t) { // CheckingTransformer {
    import symbols._

    def isImperativeFlag(f: s.Flag): Boolean = f match {
      case s.IsPure | s.IsVar | s.IsMutable => true
      case _ => false
    }

    override def transform(tpe: s.Type): t.Type = tpe match {
      case s.MutableMapType(from, to) => t.MapType(transform(from), transform(to))
      case s.TypeParameter(id, flags) if flags exists isImperativeFlag =>
        t.TypeParameter(id, flags filterNot isImperativeFlag map transform).copiedFrom(tpe)
      case s.TypeBounds(lo, hi, flags) if flags exists isImperativeFlag =>
        t.TypeBounds(transform(lo), transform(hi), flags filterNot isImperativeFlag map transform)
      case _ => super.transform(tpe)
    }

    object Lets {
      def unapply(e: s.Expr): Option[(Seq[(s.ValDef, s.Expr)], s.Expr)] = e match {
        case s.Let(vd, e0, body) => unapply(body).map {
          case (lets, rest) => ((vd, e0) +: lets, rest)
        }
        case _ => Some((Seq(), e))
      }
    }

    object ReconstructTuple {
      def unapply(e: s.Expr): Option[s.Expr] = e match {
        case s.Let(vd, tuple, Lets(lets, s.Tuple(es))) =>
          val letsMap = lets.map { case (vd, e) => (vd.id, e) }.toMap
          if (
            vd.getType.isInstanceOf[s.TupleType] &&
            es.length == vd.getType.asInstanceOf[s.TupleType].bases.length &&
            es.zipWithIndex.forall {
              case (e0 : s.Variable, i) =>
                letsMap.contains(e0.id) &&
                letsMap(e0.id) == s.TupleSelect(vd.toVariable, i + 1)
              case (e0, i) =>
                e0 == s.TupleSelect(vd.toVariable, i + 1)
            }
          )
            Some(tuple)
          else
            None

        case s.Let(vd, e, Lets(Seq(), v)) if v == vd.toVariable =>
          Some(e)

        case _ => None
      }
    }

    override def transform(expr: s.Expr): t.Expr = {
      super.transform(s.exprOps.postMap { expr => expr match {
        case s.BoolBitwiseAnd(lhs, rhs) => Some(s.And(lhs, rhs).copiedFrom(expr))
        case s.BoolBitwiseOr(lhs, rhs) => Some(s.Or(lhs, rhs).copiedFrom(expr))
        case s.BoolBitwiseXor(lhs, rhs) => Some(s.Not(s.Equals(lhs, rhs).copiedFrom(expr)).copiedFrom(expr))

        case s.Variable(id, tpe, flags) =>
          Some(s.Variable(id, tpe, flags filterNot isImperativeFlag).copiedFrom(expr))

        case s.MutableMapWithDefault(from, to, default) =>
          Some(s.FiniteMap(Seq(), s.Application(default, Seq()), from, to))
        case s.MutableMapApply(map, index) => Some(s.MapApply(map, index))
        case s.MutableMapUpdated(map, key, value) => Some(s.MapUpdated(map, key, value))
        case s.MutableMapDuplicate(map) => Some(map)

        case ReconstructTuple(tuple) => Some(tuple)

        case _ => None
      } } (expr))

    }

    override def transform(vd: s.ValDef): t.ValDef = {
      val (newId, newTpe) = transform(vd.id, vd.tpe)
      t.ValDef(newId, newTpe, (vd.flags filterNot isImperativeFlag) map transform).copiedFrom(vd)
    }
  }

  private def checkNoOld(expr: s.Expr): Unit = s.exprOps.preTraversal {
    case o @ s.Old(_) =>
      throw MalformedStainlessCode(o, s"Stainless `old` can only occur in postconditions.")
    case _ => ()
  } (expr)

  private def checkValidOldUsage(expr: s.Expr): Unit = s.exprOps.preTraversal {
    case o @ s.Old(s.ADTSelector(v: s.Variable, id)) =>
      throw MalformedStainlessCode(o,
        s"Stainless `old` can only occur on `this` and variables. Did you mean `old($v).$id`?")
    case o @ s.Old(s.ClassSelector(v: s.Variable, id)) =>
      throw MalformedStainlessCode(o,
        s"Stainless `old` can only occur on `this` and variables. Did you mean `old($v).$id`?")
    case o @ s.Old(e) =>
      throw MalformedStainlessCode(o, s"Stainless `old` is only defined on `this` and variables.")
    case _ => ()
  } (expr)

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    val (specs, body) = s.exprOps.deconstructSpecs(fd.fullBody)

    specs foreach {
      case post: s.exprOps.Postcondition =>
        // The new imperative phase allows for arbitrary expressions inside `old(...)`.
        if (!ImperativeCleanup.this.context.options.findOptionOrDefault(optFullImperative)) {
          post.traverse(checkValidOldUsage _)
        }
      case spec => spec.traverse(checkNoOld _)
    }

    body foreach checkNoOld

    super.extractFunction(context, fd.copy(flags = fd.flags filterNot context.isImperativeFlag))
  }

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = {
    super.extractSort(context, sort.copy(flags = sort.flags filterNot context.isImperativeFlag))
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = {
    super.extractClass(context, cd.copy(flags = cd.flags filterNot context.isImperativeFlag))
  }

  override protected def extractTypeDef(context: TransformerContext, td: s.TypeDef): t.TypeDef = {
    super.extractTypeDef(context, td.copy(flags = td.flags filterNot context.isImperativeFlag))
  }
}

object ImperativeCleanup {
  def apply(ts: Trees, tt: oo.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends ImperativeCleanup(s, t)
    new Impl(ts, tt)
  }
}
