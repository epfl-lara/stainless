/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._

final class StructInliner(val ctx: inox.Context) extends Transformer(RIR, SIR) with NoEnv {
  import from._

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  object SimplifiableClassDef {
    def unapply(cd: ClassDef): Option[ClassDef] = {
      if (cd.fields.length == 1 && cd.parent.isEmpty) Some(cd)
      else None
    }
  }

  object SimplifiableExpr {
    def unapply(e: Expr): Option[Expr] = e.getType match {
      case ClassType(SimplifiableClassDef(cd)) => Some(e)
      case _ => None
    }
  }

  override def rec(typ: Type)(using Env): to.Type = typ match {
    case ClassType(SimplifiableClassDef(cd)) => rec(cd.fields.head.typ)
    case _ => super.rec(typ)
  }

  override def recImpl(e: Expr)(using Env): (to.Expr, Env) = e match {
    case FieldAccess(SimplifiableExpr(obj), _) => recImpl(obj)
    case Construct(SimplifiableClassDef(cd), Seq(arg)) => recImpl(arg)
    case _ => super.recImpl(e)
  }

  override def rec(prog: Prog)(using Env): to.Prog =
    super.rec(
      prog.copy(classes =
        prog.classes.filter {
          case SimplifiableClassDef(cd) => false
          case _ => true
        }
      )
    )

}
