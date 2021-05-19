/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import CAST._

class CASTTraverser(implicit ctx: inox.Context) {

  def deconstruct(t: Tree): Seq[Tree] = t match {
    case Prog(includes, typeDefs, enums, types, functions) =>
      includes.toSeq ++ typeDefs.toSeq ++ enums.toSeq ++ types ++ functions.toSeq

    case TypeDef(orig, alias, _) =>
      Seq(orig, alias)

    case Pointer(base) =>
      Seq(base)

    case FunType(ret, params) =>
      ret +: params

    case FixedArrayType(base, _) =>
      Seq(base)

    case Struct(id, fields, _) =>
      id +: fields

    case Fun(id, returnType, params, Left(block), _) =>
      id +: returnType +: params :+ block

    case Fun(id, returnType, params, _, _) =>
      id +: returnType +: params

    case Id(name) =>
      Seq()

    case Primitive(pt) =>
      Seq()

    case Union(id, fields, _) =>
      id +: fields

    case Enum(id, literals) =>
      id +: literals

    case Var(id, typ) =>
      Seq(id, typ)

    case Block(exprs) =>
      exprs

    case Lit(lit) =>
      Seq()

    case EnumLiteral(lit) =>
      Seq()

    case Decl(id, typ) =>
      Seq(id, typ)

    case DeclInit(id, typ, value) =>
      Seq(id, typ, value)

    case DeclArrayStatic(id, base, length, values) =>
      Seq(id, base) ++ values

    case ArrayStatic(base, values) =>
      base +: values

    case DeclArrayVLA(id, base, length, defaultExpr) =>
      Seq(id, base, length, defaultExpr)

    case StructInit(struct, values) =>
      struct +: values

    case UnionInit(union, fieldId, value) =>
      Seq(union, fieldId, value)

    case Call(id, args) =>
      id +: args

    case Binding(id) =>
      Seq(id)

    case FieldAccess(Deref(obj), fieldId) =>
      Seq(obj, fieldId)

    case FieldAccess(obj, fieldId) =>
      Seq(obj, fieldId)

    case ArrayAccess(array, index) =>
      Seq(array, index)

    case Ref(e) =>
      Seq(e)

    case Deref(e) =>
      Seq(e)

    case Assign(lhs, rhs) =>
      Seq(lhs, rhs)

    case BinOp(op, lhs, rhs) =>
      Seq(lhs, rhs)

    case UnOp(op, expr) =>
      Seq(expr)

    case If(cond, thenn) =>
      Seq(cond, thenn)

    case IfElse(cond, thenn, elze) =>
      Seq(cond, thenn, elze)

    case While(cond, body) =>
      Seq(cond, body)

    case Break =>
      Seq()

    case Return(value) =>
      Seq(value)

    case Cast(expr, typ) =>
      Seq(expr, typ)

    case _ =>
      ctx.reporter.fatalError(s"Cannot deconstruct CAST tree of type ${t.getClass}")
  }

  def traverse(t: Tree): Unit = {
    deconstruct(t).foreach(traverse)
  }

}


object CASTDependencies {

  def headerDependencies(prog: Prog)(implicit ctx: inox.Context): Set[Type] = {
    var res = scala.collection.mutable.Set[Type]()

    object typeCollector extends CASTTraverser {
      override def traverse(t: Tree) = t match {
        case tp: Type =>
          res += tp
          super.traverse(t)
        case _ =>
          super.traverse(t)
      }
    }

    for (Fun(_, returnType, params, _, _) <- prog.functions.filter(_.isExported)) {
      typeCollector.traverse(returnType)
      params.foreach(typeCollector.traverse)
    }

    for (tpe <- prog.typeDefs.filter(_.isExported)) typeCollector.traverse(tpe)
    for (tpe <- prog.types.filter(_.isExported)) typeCollector.traverse(tpe)

    res.toSet
  }

}
