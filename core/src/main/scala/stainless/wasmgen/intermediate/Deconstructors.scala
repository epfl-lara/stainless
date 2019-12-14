/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen.intermediate

trait TreeDeconstructor extends stainless.ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  // Reminder:
  // protected type Deconstructed[T <: t.Tree] = (Seq[Identifier], Seq[s.Variable], Seq[s.Expr], Seq[s.Type], Seq[s.Flag], Builder[T])
  // protected type Builder[T <: t.Tree] = (Seq[Identifier], Seq[t.Variable], Seq[t.Expr], Seq[t.Type], Seq[t.Flag]) => T

  override def deconstruct(expr: s.Expr): Deconstructed[t.Expr] = expr match {
    case s.Record(tpe, fields) => (
      NoIdentifiers, NoVariables, fields, Seq(tpe), NoFlags,
      (_, _, es, tpe, _) => t.Record(tpe.head.asInstanceOf[t.RecordType], es)
    )

    case s.RecordSelector(record, selector) => (
      Seq(selector), NoVariables, Seq(record), NoTypes, NoFlags,
      (ids, _, es, _, _) => t.RecordSelector(es.head, ids.head)
    )

    case s.FunctionPointer(id) => (
      Seq(id), NoVariables, NoExpressions, NoTypes, NoFlags,
      (ids, _, _, _, _) => t.FunctionPointer(ids.head)
    )

    case s.CastDown(e, tp) => (
      NoIdentifiers, NoVariables, Seq(e), Seq(tp), NoFlags,
      (_, _, es, tps, _) => t.CastDown(es.head, tps.head.asInstanceOf[t.RecordType])
    )

    case s.CastUp(e, tp) => (
      NoIdentifiers, NoVariables, Seq(e), Seq(tp), NoFlags,
      (_, _, es, tps, _) => t.CastUp(es.head, tps.head.asInstanceOf[t.RecordType])
    )

    case s.Output(msg) => (
      NoIdentifiers, NoVariables, Seq(msg), NoTypes, NoFlags,
      (_, _, es, _, _) => t.Output(es.head)
    )

    case s.Sequence(es) => (
      NoIdentifiers, NoVariables, es, NoTypes, NoFlags,
      (_, _, es1, _, _) => t.Sequence(es1)
    )

    case s.NewArray(length, init) => (
      NoIdentifiers, NoVariables, Seq(length) ++ init, Seq(), NoFlags,
      (_, _, es, _, _) => t.NewArray(es(0), if (es.size > 1) Some(es(1)) else None)
    )

    case s.ArraySet(array, index, value) => (
      NoIdentifiers, NoVariables, Seq(array, index, value), NoTypes, NoFlags,
      (_, _, es, _, _) => t.ArraySet(es(0), es(1), es(2))
    )

    case _ => super.deconstruct(expr)
  }

  override def deconstruct(tpe: s.Type): Deconstructed[t.Type] = tpe match {
    case s.RecordType(record) => (
      Seq(record), NoVariables, NoExpressions, NoTypes, NoFlags,
      (recs, _, _, tps, _) => t.RecordType(recs.head)
    )
    case _ => super.deconstruct(tpe)
  }
}

trait Deconstructors extends stainless.ast.Deconstructors { self: Trees =>
  // FIXME: What do I have to override here?

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }

  override val deconstructor: TreeDeconstructor { val s: self.type; val t: self.type } = {
    getDeconstructor(self).asInstanceOf[TreeDeconstructor { val s: self.type; val t: self.type }]
  }
}
