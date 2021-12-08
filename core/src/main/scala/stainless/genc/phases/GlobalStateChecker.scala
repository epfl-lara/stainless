/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import extraction._
import extraction.throwing. { trees => tt }
import tt._
import extraction.imperative.TransformerWithType

import inox.utils.Position
import ExtraOps._

trait GlobalStateChecker { self =>
  val syms: tt.Symbols
  val context: inox.Context
  protected val printerOpts: tt.PrinterOptions
  protected given givenCheckerPrinterOpts: tt.PrinterOptions = printerOpts

  case object NoGlobal extends Exception
  def noGlobalFor(cid: Identifier) = {
    class NoGlobalFor(override val s: tt.type, override val t: tt.type)
                     (using override val symbols: syms.type)
      extends TransformerWithType {
      override def transform(expr: Expr, tpe: Type): Expr = tpe match {
        case ct: ClassType if isGlobal(ct) && ct.id == cid =>
          context.reporter.fatalError(expr.getPos, "Global state is not allowed in expression: " + expr.asString)
        case _ =>
          try super.transform(expr, tpe)
          catch {
            case NoGlobal => context.reporter.fatalError(expr.getPos, "Global state is not allowed in expression: " + expr.asString)
          }
      }

      override def transform(tpe: Type): Type = tpe match {
        case ct: ClassType if isGlobal(ct) && ct.id == cid => throw NoGlobal
        case _ => super.transform(tpe)
      }
    }
    new NoGlobalFor(tt, tt)(using syms)
  }

  def useOnly(cid: Identifier, globalStateId: Identifier) = {
    class UseOnly(override val s: tt.type, override val t: tt.type)
                 (using override val symbols: syms.type)
      extends TransformerWithType{
      override def transform(expr: Expr, tpe: Type): Expr = (expr, tpe) match {
        // This is the only global state declaration (for `cid`) which is allowed
        case (Let(vd, _, _), _) if vd.id == globalStateId => expr

        // Global state accesses are allowed on `id` or `old(id)`
        case (ClassSelector(Variable(`globalStateId`, _, _), _), _) => expr
        case (ClassSelector(Old(Variable(`globalStateId`, _, _)), _), _) => expr

        // Global state assignments are allowed on `id`
        case (FieldAssignment(Variable(`globalStateId`, _, _), _, expr2), _) => transform(expr2)

        // Global state can be passed to other functions
        case (FunctionInvocation(id, tps, args), _) =>
          val (beforeGlobal, globalArgumentAndAfter) = args.span {
            case Variable(`globalStateId`, _, _) => false
            case _ => true
          }
          beforeGlobal.map(transform(_, tpe))
          if (globalArgumentAndAfter.nonEmpty)
            globalArgumentAndAfter.tail.map(transform(_, tpe))
          expr

        case (_, ct: ClassType) if isGlobal(ct) && ct.id == cid =>
          context.reporter.fatalError(expr.getPos, "Global state is not allowed in expression: " + expr.asString)
        case _ =>
          try super.transform(expr, tpe)
          catch {
            case NoGlobal => context.reporter.fatalError(expr.getPos, "Global state is not allowed in expression: " + expr.asString)
          }
      }

      override def transform(tpe: Type): Type = tpe match {
        case ct: ClassType if isGlobal(ct) && ct.id == cid => throw NoGlobal
        case _ => super.transform(tpe)
      }
    }
    new UseOnly(tt, tt)(using syms)
  }

  def checkGlobalUsage(): Unit = {
    // * Functions can take as argument at most one instance of ``GlobalState``.
    // * There can be at most one instance of ``GlobalState`` created
    //     (in a function that doesn't already take an instance as argument).
    // * A ``GlobalState`` instance can only be used for reads and assignments
    //      (e.g. it cannot be let bound, except for the declaration mentioned above).
    // * The only global state that can be passed to other functions is the one we create
    //      or the one we received as a function argument.
    for (globalClass <- syms.classes.values.toSeq.filter(_.isGlobal)) {
      val noGlobal = noGlobalFor(globalClass.id)
      val paramInits = syms.paramInits(globalClass.id)
      val invOpt: Option[FunDef] = globalClass.flags.collectFirst { case HasADTInvariant(inv) => syms.getFunction(inv) }
      for (fd <- syms.functions.values if invOpt.forall(inv => fd.id != inv.id)) {
        val globalParams = fd.params.filter { vd => vd.tpe match {
          case ClassType(id, _) => id == globalClass.id
          case _ => false
        }}
        val globalParamsLength = globalParams.length
        if (globalParamsLength == 0) {
          // in functions which do not take global state as argument, we allow one declaration
          // of a global state with the default values
          val declarations = exprOps.collect[(ValDef, Seq[Expr])] {
            case Let(vd, ClassConstructor(ct, args), body) if ct.id == globalClass.id =>
              Set((vd, args))
            case _ => Set()
          }(fd.fullBody)
          if (declarations.size == 0) {
            // no declaration and no global state passed in function, so global state cannot be used at all
            noGlobal.transform(fd.fullBody)
          } else if (declarations.size == 1) {
            val (vd, args) = declarations.head
            if (globalClass.isGlobalDefault) {
              if (
                args.length != paramInits.length ||
                !(args.zip(paramInits).forall {
                  case (arg, paramInit) => arg == paramInit.fullBody
                })
              ) {
                context.reporter.fatalError(vd.getPos,
                  "Creating an instance of a state marked `@cCode.global` is only allowed by invoking the default constructor (with the default arguments)"
                )
              }
            } else
              context.reporter.warning(vd.getPos,
                "Initialization of global state in Scala might not correspond to default initialization of C"
              )
            // we can do reads and assignments on the declared global state, and pass it to other functions
            useOnly(globalClass.id, vd.id).transform(fd.fullBody)
          } else {
            context.reporter.fatalError(declarations.tail.head._1.getPos,
              s"There can be at most one declaration for a global state of class ${globalClass.id.asString}"
            )
          }
        } else if (globalParamsLength == 1) {
          // in functions which take a global state argument, we can do reads/assignments on the
          // global state, and we can pass the global state to other functions
          useOnly(globalClass.id, globalParams.head.id).transform(fd.fullBody)
        } else {
          context.reporter.fatalError(fd.getPos,
            s"There can be at most one global state from class ${globalClass.id.asString} " +
            s"as argument of function ${fd.id.asString}"
          )
        }
      }
    }
  }

}
