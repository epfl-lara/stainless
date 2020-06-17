/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package trace

trait Trace extends CachingPhase with SimpleFunctions with IdentitySorts { self =>
  val s: Trees
  val t: termination.Trees
  import s._

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({(fd, symbols) => 
    FunctionKey(fd) + SetKey(
      symbols.dependencies(fd.id)
        .flatMap(id => symbols.lookupFunction(id))
    )
  })

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private[this] object identity extends transformers.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def extractFunction(symbols: Symbols, fd: FunDef): t.FunDef = {
    import symbols._
    var funInv: Option[FunctionInvocation] = None

    if(fd.flags.exists(elem => elem.name == "traceInduct")) {
      fd.flags.filter(elem => elem.name == "traceInduct").head match {
        case Annotation("traceInduct", fun) => {
          exprOps.preTraversal {
            case _ if funInv.isDefined => // do nothing
            case fi @ FunctionInvocation(tfd, _, args) if symbols.isRecursive(tfd) && (fun.contains(StringLiteral(tfd.name)) || fun.contains(StringLiteral("")))
            => {
                  val paramVars = fd.params.map(_.toVariable)
                  val argCheck = args.forall(paramVars.contains) && args.toSet.size == args.size
                  if (argCheck) 
                    funInv = Some(fi)
                }
            case _ => 
          }(fd.fullBody)
        }
      }
    }

    val result: FunDef = (funInv match {
      case None => fd
      case Some(finv) => createTactFun(symbols, fd, finv)
    })

    identity.transform(result.copy(flags = result.flags filterNot (f => f == TraceInduct)))    
  }
  
  private def createTactFun(symbols: Symbols, function: FunDef, finv: FunctionInvocation): FunDef = {
    import symbols._

    val callee: FunDef = symbols.functions.filter(elem => elem._2.id == finv.id).head._2

    def inductPattern(e: Expr): Expr = {
      e match {
        case IfExpr(c, th, el) =>
          andJoin(Seq(inductPattern(c), IfExpr(c, inductPattern(th), inductPattern(el))))
        case MatchExpr(scr, cases) =>
          val scrpat = inductPattern(scr)
          val casePats = cases.map {
            case MatchCase(pat, optGuard, rhs) =>
              val guardPat = optGuard.toSeq.map(inductPattern _)
              (guardPat, MatchCase(pat, optGuard, inductPattern(rhs)))
          }
          val pats = scrpat +: casePats.flatMap(_._1) :+ MatchExpr(scr, casePats.map(_._2))
          andJoin(pats)
        case Let(i, v, b) =>
          andJoin(Seq(inductPattern(v), Let(i, v, inductPattern(b))))
        case FunctionInvocation(tfd, _, args) =>
          val argPattern = andJoin(args.map(inductPattern))
          if (tfd == callee.id) { // self recursive call ?
            // create a tactFun invocation to mimic the recursion pattern
            val paramVars = function.params.map(_.toVariable)
            val paramIndex = paramVars.zipWithIndex.toMap
            val framePositions = finv.args.zipWithIndex.collect {
              case (v: Variable, i) if paramVars.contains(v) => (v, i)
            }.toMap
            val footprint = paramVars.filterNot(framePositions.keySet.contains)
            val indexedFootprint = footprint.map { a => paramIndex(a) -> a }.toMap
            // create a tactFun invocation to mimic the recursion pattern
            val indexedArgs = framePositions.map {
              case (f, i) => paramIndex(f) -> args(i)
            }.toMap ++ indexedFootprint
            val recArgs = (0 until indexedArgs.size).map(indexedArgs)
            val recCall = FunctionInvocation(function.id, function.typeArgs, recArgs)

            andJoin(Seq(argPattern, recCall))
          } else {
            argPattern
          }
        case Operator(args, op) =>
          // conjoin all the expressions and return them
          andJoin(args.map(inductPattern))
      }
    }

    val argsMap = callee.params.map(_.toVariable).zip(finv.args).toMap
    val tparamMap = callee.typeArgs.zip(finv.tfd.tps).toMap
    val inlinedBody = typeOps.instantiateType(exprOps.replaceFromSymbols(argsMap, callee.body.get), tparamMap)
    val inductScheme = inductPattern(inlinedBody)

    val prevBody = function.fullBody match {
      case Ensuring(body, pred) => body
      case _ => function.fullBody
    }

    // body, pre and post for the tactFun

    val body = andJoin(Seq(inductScheme, prevBody))
    val precondition = function.precondition
    val postcondition = function.postcondition
 
    val bodyPre = exprOps.withPrecondition(body, precondition)
    val bodyPost = exprOps.withPostcondition(bodyPre,postcondition)

    function.copy(function.id, function.tparams, function.params, function.returnType, bodyPost, function.flags)
  }

}


object Trace {
  def apply(ts: Trees, tt: termination.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new Trace {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}