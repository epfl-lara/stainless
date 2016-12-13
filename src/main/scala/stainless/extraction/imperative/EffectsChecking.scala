/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait EffectsChecking extends inox.ast.SymbolTransformer {
  val s: Trees
  val t: Trees

  def transform(syms: s.Symbols): t.Symbols = {
    val effectsAnalysis = new EffectsAnalysis

    allFunDefs(pgm).foreach(fd => {

      checkPureAnnotation(fd, effectsAnalysis)(ctx)
      checkAliasing(fd, effectsAnalysis)(ctx)

      fd.postcondition.foreach{ case post@Lambda(vds, body) => {
        val effects = effectsAnalysis(body)
        if(effects.nonEmpty) {
          ctx.reporter.fatalError(post.getPos, "Postcondition has effects on: " + effects.head)
        }
      }}

      fd.precondition.foreach(pre => {
        val effects = effectsAnalysis(pre)
        if(effects.nonEmpty) {
          ctx.reporter.fatalError(pre.getPos, "Precondition has effects on: " + effects.head)
        }
      })

      fd.body.foreach(body => {
        preTraversal{
          case Assert(pred, _, _) => {
            val effects = effectsAnalysis(pred)
            if(effects.nonEmpty) {
              ctx.reporter.fatalError(pred.getPos, "Assertion has effects on: " + effects.head)
            }
          }
          case wh@While(_, _) => {
            wh.invariant.foreach(invariant => {
              val effects = effectsAnalysis(invariant) 
              if(effects.nonEmpty) {
                ctx.reporter.fatalError(invariant.getPos, "Loop invariant has effects on: " + effects.head)
              }
            })
          }
          case m@MatchExpr(_, cses) => {
            cses.foreach(cse => {
              cse.optGuard.foreach(guard => {
                val effects = effectsAnalysis(guard)
                if(effects.nonEmpty) {
                  ctx.reporter.fatalError(guard.getPos, "Pattern guard has effects on: " + effects.head)
                }
              })

              PatternOps.preTraversal{
                case pat@UnapplyPattern(_, unapply, _) => {
                  val effects = effectsAnalysis(unapply.fd)
                  if(effects.nonEmpty) {
                    ctx.reporter.fatalError(pat.getPos, "Pattern unapply has effects on: " + effects.head)
                  }
                }
                case _ => ()
              }(cse.pattern)
              
            })
          }
          case _ => ()
        }(body)
      })

    })
  }

  /*
   * Checks and reports error if a function is annotated as pure and still has effects.
   * Maybe it would be good in the future to merge this @pure annotation with the report
   * from the AnalysisPhase, but until a good design is found we just implement this quick
   * error reporting here.
   */
  private def checkPureAnnotation(fd: FunDef, effects: EffectsAnalysis)(ctx: LeonContext): Unit = {
    if(fd.annotations.contains("pure")) {
      if(effects(fd).nonEmpty) {
        ctx.reporter.fatalError(fd.getPos, "Function annotated @pure has effects.")
      }
    }
  }


  private def checkAliasing(fd: FunDef, effects: EffectsAnalysis)(ctx: LeonContext): Unit = {
    def checkReturnValue(body: Expr, bindings: Set[Identifier]): Unit = {
      getReturnedExpr(body).foreach{
        case expr if effects.isMutableType(expr.getType) => 
          findReceiverId(expr).foreach(id =>
            if(bindings.contains(id))
              ctx.reporter.fatalError(expr.getPos, "Cannot return a shared reference to a mutable object: " + expr)
          )
        case _ => ()
      }
    }

    if(fd.canBeField && effects.isMutableType(fd.returnType))
      ctx.reporter.fatalError(fd.getPos, "A global field cannot refer to a mutable object")
    
    fd.body.foreach(bd => {
      val params = fd.params.map(_.id).toSet
      checkReturnValue(bd, params)
      preMapWithContext[Set[Identifier]]((expr, bindings) => expr match {
        case l@Let(id, v, b) if effects.isMutableType(v.getType) => {
          if(!isExpressionFresh(v, effects))
            ctx.reporter.fatalError(v.getPos, "Illegal aliasing: " + v)
          (None, bindings + id)
        }
        case l@LetVar(id, v, b) if effects.isMutableType(v.getType) => {
          if(!isExpressionFresh(v, effects))
            ctx.reporter.fatalError(v.getPos, "Illegal aliasing: " + v)
          (None, bindings + id)
        }
        case l@LetDef(fds, body) => {
          fds.foreach(fd => fd.body.foreach(bd => checkReturnValue(bd, bindings)))
          (None, bindings)
        }

        case CaseClass(ct, args) => {
          ct.classDef.tparams.zip(ct.tps).foreach{ case (typeParam, instanceType) => {
            if(effects.isMutableType(instanceType) && !typeParam.tp.isMutable) {
              ctx.reporter.fatalError(expr.getPos, "Cannot instantiate a non-mutable type parameter with a mutable type")
            }
          }}
          (None, bindings)
        }

        case _ => (None, bindings)
      })(bd, params)
    })
  }


  /*
   * A fresh expression is an expression that is newly created
   * and does not share memory with existing values and variables.
   *
   * If the expression is made of existing immutable variables (Int or
   * immutable case classes), it is considered fresh as we consider all
   * non mutable objects to have a value-copy semantics.
   *
   * It turns out that an expression of non-mutable type is always fresh,
   * as it can not contains reference to a mutable object, by definition
   */
  private def isExpressionFresh(expr: Expr, effects: EffectsAnalysis): Boolean = {
    !effects.isMutableType(expr.getType) || (expr match {
      case v@Variable(_) => !effects.isMutableType(v.getType)
      case CaseClass(_, args) => args.forall(arg => isExpressionFresh(arg, effects))

      case FiniteArray(elems, default, _) => elems.forall(p => isExpressionFresh(p._2, effects)) && default.forall(e => isExpressionFresh(e, effects))

      //function invocation always return a fresh expression, by hypothesis (global assumption)
      case FunctionInvocation(_, _) => true

      //ArrayUpdated returns a mutable array, which by definition is a clone of the original
      case ArrayUpdated(_, _, _) => true

      //any other expression is conservately assumed to be non-fresh if
      //any sub-expression is non-fresh (i.e. an if-then-else with a reference in one branch)
      case Operator(args, _) => args.forall(arg => isExpressionFresh(arg, effects))
    })
  }

  /*
   * returns all fun def in the program, including local definitions inside
   * other functions (LetDef).
   */
  private def allFunDefs(pgm: Program): Seq[FunDef] =
      pgm.definedFunctions.flatMap(fd => 
        fd.body.toSet.flatMap((bd: Expr) =>
          nestedFunDefsOf(bd)) + fd)


  /*
   * A bit hacky, but not sure of the best way to do something like that
   * currently.
   */
  private def getReturnedExpr(expr: Expr): Seq[Expr] = expr match {
    case Let(_, _, rest) => getReturnedExpr(rest)
    case LetVar(_, _, rest) => getReturnedExpr(rest)
    case Block(_, rest) => getReturnedExpr(rest)
    case IfExpr(_, thenn, elze) => getReturnedExpr(thenn) ++ getReturnedExpr(elze)
    case MatchExpr(_, cses) => cses.flatMap{ cse => getReturnedExpr(cse.rhs) }
    case e => Seq(expr)
  }


  private def findReceiverId(o: Expr): Option[Identifier] = o match {
    case Variable(id) => Some(id)
    case CaseClassSelector(_, e, _) => findReceiverId(e)
    case AsInstanceOf(e, ct) => findReceiverId(e)
    case ArraySelect(a, _) => findReceiverId(a)
    case _ => None
  }

}
