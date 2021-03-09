/* Copyright 2009-2021 EPFL, Lausanne */

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

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    import symbols._
    import trees._

    val models = symbols.functions.values.toList.filter(elem => isModel(elem.id)).map(elem => elem.id)
    val functions = symbols.functions.values.toList.filter(elem => shouldBeChecked(elem.id)).map(elem => elem.id)
   
    if (Trace.getModels.isEmpty) {
      Trace.setModels(models)
      Trace.nextModel
    }
    if (Trace.getFunctions.isEmpty) {
      Trace.setFunctions(functions)
      Trace.nextFunction
    }

    var localCounter = 0

    def freshId(a: Identifier, b: Identifier): Identifier = {
      localCounter = localCounter + 1
      new Identifier(fixedFullName(a)+"$"+fixedFullName(b),localCounter,localCounter)
    }

    //if (fd1 != fd2) && (fd1.params.size == fd2.params.size)
    def checkPair(fd1: s.FunDef, fd2: s.FunDef): s.FunDef = {

      val newParams = fd1.params.map{param => param.freshen}
      val newParamVars = newParams.map{param => param.toVariable}
      val newParamTypes = fd1.tparams.map{tparam => tparam.freshen}
      val newParamTps = newParamTypes.map{tparam => tparam.tp}

      val vd = s.ValDef.fresh("holds", s.BooleanType())
      val post = s.Lambda(Seq(vd), vd.toVariable)

      val body = s.Ensuring(s.Equals(s.FunctionInvocation(fd1.id, newParamTps, newParamVars), s.FunctionInvocation(fd2.id, newParamTps, newParamVars)), post)
      val flags: Seq[s.Flag] = Seq(s.Derived(fd1.id), s.Annotation("traceInduct",List(StringLiteral(fd1.id.name))))

      new s.FunDef(freshId(fd1.id, fd2.id), newParamTypes, newParams, s.BooleanType(), body, flags)
    }

    def newFuns: List[s.FunDef] = (Trace.getModel, Trace.getFunction) match {
      case (Some(model), Some(function)) => {
        val m = symbols.functions.filter(elem => elem._2.id == model).head._2
        val f = symbols.functions.filter(elem => elem._2.id == function).head._2
        val newFun = checkPair(m, f)
        Trace.setTrace(newFun.id)
        List(newFun)
      }
      case _ => Nil
    }

/*
    def newFuns: List[s.FunDef] = Trace.nextModel match {
      case Some(model) => toCheck.map(f => checkPair(

        symbols.functions.filter(elem => elem._2.id == model).head._2

    , f))
      case None => check(toCheck, toCheck, Nil)
    }

    def check(funs1: List[s.FunDef], funs2: List[s.FunDef], acc: List[s.FunDef]): List[s.FunDef] = {
      funs1 match {
        case Nil => acc
        case fd1::xs1 => {
          funs2 match {
            case Nil => check(xs1, toCheck, acc)
              //todo: check if both funs have same arg list
            case fd2::xs2 if (fd1 != fd2) && (fd1.params.size == fd2.params.size) =>
              check(funs1, xs2, checkPair(fd1, fd2)::acc)
            case _ => check(funs1, funs2.tail, acc)
          }
        }
      }
    }
*/
    val extracted = super.extractSymbols(context, symbols)
    //newFuns(toCheck, toCheck, Nil).map(f => extractFunction(symbols, f))
    registerFunctions(extracted, newFuns.map(f => extractFunction(symbols, f)))
  }

  override protected def extractFunction(symbols: Symbols, fd: FunDef): t.FunDef = {
    import symbols._
    var funInv: Option[FunctionInvocation] = None

    if(fd.flags.exists(elem => elem.name == "traceInduct")) {
      fd.flags.filter(elem => elem.name == "traceInduct").head match {
        case Annotation("traceInduct", fun) => {
          exprOps.preTraversal {
            case _ if funInv.isDefined => // do nothing
            case fi @ FunctionInvocation(tfd, _, args) if symbols.isRecursive(tfd) && (fun.contains(StringLiteral(tfd.name)) || fun.contains(StringLiteral(""))) => { 
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
    val precondition = exprOps.preconditionOf(function.fullBody)  //function.precondition
    val postcondition = exprOps.postconditionOf(function.fullBody) //function.postcondition
    val bodyPre = exprOps.withPrecondition(body, precondition)
    val bodyPost = exprOps.withPostcondition(bodyPre,postcondition)
    function.copy(function.id, function.tparams, function.params, function.returnType, bodyPost, function.flags)  

  }

//from CheckFilter.scala
  type Path = Seq[String]
  private def fullNameToPath(fullName: String): Path = (fullName split '.').toSeq

  // TODO this is probably done somewhere else in a cleaner fasion...
  private def fixedFullName(id: Identifier): String = id.fullName
    .replaceAllLiterally("$bar", "|")
    .replaceAllLiterally("$up", "^")
    .replaceAllLiterally("$eq", "=")
    .replaceAllLiterally("$plus", "+")
    .replaceAllLiterally("$minus", "-")
    .replaceAllLiterally("$times", "*")
    .replaceAllLiterally("$div", "/")
    .replaceAllLiterally("$less", "<")
    .replaceAllLiterally("$geater", ">")
    .replaceAllLiterally("$colon", ":")
    .replaceAllLiterally("$amp", "&")
    .replaceAllLiterally("$tilde", "~")


  private lazy val pathsOpt: Option[Seq[Path]] = context.options.findOption(optCompareFuns) map { functions =>
    functions map fullNameToPath
  }

  private def shouldBeChecked(fid: Identifier): Boolean = pathsOpt match {
    case None => false

    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumes.
      val path: Path = fullNameToPath(fixedFullName(fid))
      paths exists { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
  }

  private lazy val pathsOptModels: Option[Seq[Path]] = context.options.findOption(optModels) map { functions =>
    functions map fullNameToPath
  }

  private def isModel(fid: Identifier): Boolean = pathsOptModels match {
    case None => false

    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumes.
      val path: Path = fullNameToPath(fixedFullName(fid))
      paths exists { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
  }

}


object Trace {
  var boxes: Map[Identifier, List[Identifier]] = Map()
  var errors: List[Identifier] = List()
  var unknowns: List[Identifier] = List()

  def printEverything() = {
    System.out.println("boxes")   
    System.out.println(boxes)
    System.out.println("errors")
    System.out.println(errors)
    System.out.println("unknowns")
    System.out.println(unknowns)
  }

  var allModels: List[Identifier] = List()
  var tmpModels: List[Identifier] = List()

  var allFunctions: List[Identifier] = List()
  var tmpFunctions: List[Identifier] = List()

  var model: Option[Identifier] = None
  var function: Option[Identifier] = None
  var trace: Option[Identifier] = None

  def apply(ts: Trees, tt: termination.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new Trace {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }

  def setModels(m: List[Identifier]) = {
    allModels = m
    tmpModels = m
    boxes = (m zip m.map(_ => Nil)).toMap
  }

  def setFunctions(f: List[Identifier]) = {
    allFunctions = f
    tmpFunctions = f
  }

  def getModels = allModels

  def getFunctions = allFunctions


  //model for the current iteration
  def getModel = model

  //function to check in the current iteration
  def getFunction = function

  def setTrace(t: Identifier) = trace = Some(t)
  def getTrace = trace

  //iterate model for the current function
  def nextModel = (tmpModels, allModels) match {
    case (x::xs, _) => { // check the next model for the current function
      tmpModels = xs
      model = Some(x)
    }
    case (Nil, x::xs) => {
      tmpModels = allModels
      model = Some(x)
      tmpModels = xs
      function = tmpFunctions match {
        case x::xs => {
          tmpFunctions = xs
          Some(x)
        }
        case Nil => None
      }
    }
    case _ => model = None
  }

  //iterate function to check; reset model
  def nextFunction = tmpFunctions match {
    case x::xs => {
      tmpFunctions = xs
      function = Some(x)
      tmpModels = allModels
      tmpModels match {
        case Nil => model = None
        case x::xs => {
          model = Some(x)
          tmpModels = xs
        }
      }
      function
    }
    case Nil => {
      function = None
    }
  }

  def isDone = function == None

  def reportError = {
    errors = function.get::errors
    nextFunction
  }

  def reportUnknown = {
    nextModel
    if(model == None){
      unknowns = function.get::unknowns
      nextFunction
    }
  }

  def reportValid = {
    boxes = boxes + (model.get -> (function.get::boxes(model.get)))
    nextFunction
  }
}