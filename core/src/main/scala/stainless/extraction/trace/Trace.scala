/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package trace

import stainless.utils.CheckFilter

trait Trace extends CachingPhase with IdentityFunctions with IdentitySorts { self =>
  val s: Trees
  val t: termination.Trees
  import s._

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private[this] object identity extends transformers.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    import symbols._
    import exprOps._

    if (Trace.getModels.isEmpty) {
      val models = symbols.functions.values.toList.filter(elem => !elem.flags.exists(_.name == "library") &&
        isModel(elem.id)).map(elem => elem.id)
      Trace.setModels(models)
      Trace.nextModel
    }

    if (Trace.getFunctions.isEmpty) {
      val functions = symbols.functions.values.toList.filter(elem => !elem.flags.exists(_.name == "library") &&
        shouldBeChecked(elem.id)).map(elem => elem.id)
      Trace.setFunctions(functions)
      Trace.nextFunction
    }

    def generateEqLemma: Option[s.FunDef] = {
      def equivalenceChek(fd1: s.FunDef, fd2: s.FunDef): s.FunDef = {
        val id = FreshIdentifier(CheckFilter.fixedFullName(fd1.id)+"$"+CheckFilter.fixedFullName(fd2.id))

        val newParams = fd1.params.map{param => param.freshen}
        val newParamVars = newParams.map{param => param.toVariable}
        val newParamTypes = fd1.tparams.map{tparam => tparam.freshen}
        val newParamTps = newParamTypes.map{tparam => tparam.tp}

        val body = s.UnitLiteral()
        val returnType = s.UnitType()

        val specsMap = (fd1.params zip newParamVars).toMap
        val specs = BodyWithSpecs(fd1.fullBody).specs.filter(s => s.kind == LetKind || s.kind == PreconditionKind) 
        val pre = specs.map(spec => spec match {
          case Precondition(cond) => Precondition(exprOps.replaceFromSymbols(specsMap, cond))
          case LetInSpec(vd, expr) => LetInSpec(vd, exprOps.replaceFromSymbols(specsMap, expr))
          case s => s
        })

        val res = s.ValDef.fresh("res", s.UnitType())
        val cond = s.Equals(s.FunctionInvocation(fd1.id, newParamTps, newParamVars), s.FunctionInvocation(fd2.id, newParamTps, newParamVars))
        val post = Postcondition(Lambda(Seq(res), cond))

        val withPre = exprOps.reconstructSpecs(pre, Some(body), s.UnitType())
        val fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed

        val flags: Seq[s.Flag] = Seq(s.Derived(fd1.id), s.Annotation("traceInduct",List(StringLiteral(fd1.id.name))))

        new s.FunDef(id, newParamTypes, newParams, returnType, fullBody, flags)
      }

      (Trace.getModel, Trace.getFunction) match {
        case (Some(model), Some(function)) => {
          val m = symbols.functions(model)
          val f = symbols.functions(function)
          if (m.params.size == f.params.size) {
            val newFun = equivalenceChek(m, f)
            //Trace.setTrace(newFun.id)
            Some(newFun)
          }
          else {
            Trace.reportWrong
            None
          }
        }
        case _ => None
      }
    }

    val functions = generateEqLemma match {
      case Some(lemma) => lemma +: symbols.functions.values.toList
      case None => symbols.functions.values.toList
    }

    val inductFuns = functions.toList.flatMap(fd => if (fd.flags.exists(elem => elem.name == "traceInduct")) {
      //find the model for fd
      var funInv: Option[s.FunctionInvocation] = None
      fd.flags.filter(elem => elem.name == "traceInduct").head match {
        case s.Annotation("traceInduct", fun) => {
          s.exprOps.preTraversal {
            case _ if funInv.isDefined => // do nothing
            case fi @ s.FunctionInvocation(tfd, _, args) if symbols.isRecursive(tfd) && (fun.contains(StringLiteral(tfd.name)) || fun.contains(StringLiteral("")))
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

      funInv match {
        case Some(finv) => {
          // make a helper lemma:
          val helper = inductPattern(symbols, symbols.functions(finv.id), fd)

          // transform the main lemma
          val proof = FunctionInvocation(helper.id, fd.tparams.map(_.tp), fd.params.map(_.toVariable))
          val body = Let(s.ValDef.fresh("ind$proof", helper.returnType), proof, exprOps.withoutSpecs(fd.fullBody).get)
          val withPre = exprOps.reconstructSpecs(BodyWithSpecs(fd.fullBody).specs, Some(body), fd.returnType)
          val lemma = fd.copy(
            fullBody = BodyWithSpecs(withPre).reconstructed,
            flags = (s.Derived(fd.id) +: s.Derived(finv.id) +: (fd.flags.filterNot(f => f.name == "traceInduct"))).distinct
          ).copiedFrom(fd)

          Trace.setTrace(helper.id, lemma.id)
          List(helper, lemma)
        }
        case None => List()
      }
    } else List())

    val extractedSymbols = super.extractSymbols(context, symbols)
    
    val extracted = t.NoSymbols
      .withSorts(extractedSymbols.sorts.values.toSeq)
      .withFunctions(extractedSymbols.functions.values.filterNot(fd => fd.flags.exists(elem => elem.name == "traceInduct")).toSeq)

    registerFunctions(extracted, inductFuns.map(fun => identity.transform(fun)))
  }

  def inductPattern(symbols: s.Symbols, model: FunDef, lemma: FunDef) = {
    import symbols._
    import exprOps._

    val id = FreshIdentifier(lemma.id+"$induct")

    val newParams = model.params.map{param => param.freshen}
    val newParamVars = newParams.map{param => param.toVariable}
    val newParamTypes = model.tparams.map{tparam => tparam.freshen}
    val newParamTps = newParamTypes.map{tparam => tparam.tp}

    val returnType = model.returnType
    val flags = Seq(s.Derived(lemma.id), s.Derived(model.id))

    val fi = FunctionInvocation(model.id, newParamTps, newParamVars)

    /*val body = FunctionInvocation(
      ast.SymbolIdentifier("stainless.lang.specialize"),
      fi.tps,
      Seq(fi)
    )*/

    val body = FunctionInvocation(model.id, newParamTps, newParamVars)
    val indPattern = new s.FunDef(id, newParamTypes, newParams, returnType, body, flags)

    class Specializer(
      origFd: FunDef,
      newId: Identifier,
      vsubst: Map[Identifier, Expr]
    ) extends s.SelfTreeTransformer {

      override def transform(expr: s.Expr): t.Expr = expr match {
        case v: Variable =>
          vsubst.getOrElse(v.id, super.transform(v))

        case fi: FunctionInvocation if fi.id == origFd.id =>
          val fi1 = FunctionInvocation(newId, tps = fi.tps, args = fi.args)
          super.transform(fi1.copiedFrom(fi))

        case _ => super.transform(expr)
      }
    }

    val subst = (model.params.map(_.id) zip fi.args).toMap
    val specializer = new Specializer(model, indPattern.id, subst)
    
    val fullBodySpecialized = specializer.transform(exprOps.withoutSpecs(model.fullBody).get)

    val specsMap = (lemma.params zip newParamVars).toMap ++ (model.params zip newParamVars).toMap
    val specs = BodyWithSpecs(model.fullBody).specs ++ BodyWithSpecs(lemma.fullBody).specs.filterNot(_.kind == MeasureKind)

    val pre = specs.filterNot(_.kind == PostconditionKind).map(spec => spec match {
      case Precondition(cond) => Precondition(exprOps.replaceFromSymbols(specsMap, cond)).setPos(spec)
      case LetInSpec(vd, expr) => LetInSpec(vd, exprOps.replaceFromSymbols(specsMap, expr)).setPos(spec)
      case Measure(measure) => Measure(exprOps.replaceFromSymbols(specsMap, measure)).setPos(spec)
      case s => s
    })
    val withPre = exprOps.reconstructSpecs(pre, Some(fullBodySpecialized), indPattern.returnType)

    val speccedLemma = BodyWithSpecs(lemma.fullBody).addPost
    val speccedOrig = BodyWithSpecs(model.fullBody).addPost
    val postLemma = speccedLemma.getSpec(PostconditionKind).map(post => exprOps.replaceFromSymbols(specsMap, post.expr))
    val postOrig = speccedOrig.getSpec(PostconditionKind).map(post => exprOps.replaceFromSymbols(specsMap, post.expr))
    
    (postLemma, postOrig) match {
      case (Some(Lambda(Seq(res1), cond1)), Some(Lambda(Seq(res2), cond2))) => 
        val res = ValDef.fresh("res", indPattern.returnType)
        val freshCond1 = exprOps.replaceFromSymbols(Map(res1 -> res.toVariable), cond1)
        val freshCond2 = exprOps.replaceFromSymbols(Map(res2 -> res.toVariable), cond2)
        val cond = andJoin(Seq(freshCond1, freshCond2))
        val post = Postcondition(Lambda(Seq(res), cond))

        indPattern.copy(
          fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed
        ).copiedFrom(indPattern)
    }

  }

  type Path = Seq[String]

  private lazy val pathsOpt: Option[Seq[Path]] = context.options.findOption(optCompareFuns) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  private def shouldBeChecked(fid: Identifier): Boolean = pathsOpt match {
    case None => false

    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumed.
      val path: Path = CheckFilter.fullNameToPath(CheckFilter.fixedFullName(fid))
      paths exists { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
  }

  private lazy val pathsOptModels: Option[Seq[Path]] = context.options.findOption(optModels) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  private def isModel(fid: Identifier): Boolean = pathsOptModels match {
    case None => false

    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumed.
      val path: Path = CheckFilter.fullNameToPath(CheckFilter.fixedFullName(fid))
      paths exists { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
  }

}

object Trace {
  var clusters: Map[Identifier, List[Identifier]] = Map()
  var errors: List[Identifier] = List()
  var unknowns: List[Identifier] = List()
  var wrong: List[Identifier] = List() //bad signature

  def optionsError(implicit ctx: inox.Context): Boolean = 
    !ctx.options.findOptionOrDefault(frontend.optBatchedProgram) && 
    (!ctx.options.findOptionOrDefault(optModels).isEmpty || !ctx.options.findOptionOrDefault(optCompareFuns).isEmpty)
        
  def printEverything(implicit ctx: inox.Context) = {
    import ctx.{ reporter, timers }
    if(!clusters.isEmpty || !errors.isEmpty || !unknowns.isEmpty) {
      reporter.info(s"Printing equivalence checking results:")  
      allModels.foreach(model => {
        val l = clusters(model).map(CheckFilter.fixedFullName).mkString(", ")
        reporter.info(s"List of functions that are equivalent to model $CheckFilter.fixedFullName(model): $l")
      })

      val errorneous = errors.map(CheckFilter.fixedFullName).mkString(", ")
      reporter.info(s"List of erroneous functions: $errorneous")
      val timeouts = unknowns.map(CheckFilter.fixedFullName).mkString(", ")
      reporter.info(s"List of timed-out functions: $timeouts")
      val wrongs = wrong.map(CheckFilter.fixedFullName).mkString(", ")
      reporter.info(s"List of wrong functions: $wrongs")
    }
  }

  var allModels: List[Identifier] = List()
  var tmpModels: List[Identifier] = List()

  var allFunctions: List[Identifier] = List()
  var tmpFunctions: List[Identifier] = List()

  var model: Option[Identifier] = None
  var function: Option[Identifier] = None
  var trace: Option[(Identifier, Identifier)] = None

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
    clusters = (m zip m.map(_ => Nil)).toMap
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

  def setTrace(t: Identifier, i: Identifier) = trace = Some(t, i)

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

  def nextIteration[T <: AbstractReport[T]](report: AbstractReport[T])(implicit context: inox.Context): Boolean = trace match {
    case Some((t, i)) => {
      if (report.hasError(t) || report.hasError(i)) reportError
      else if (report.hasUnknown(t) || report.hasError(i)) reportUnknown
      else reportValid
      !isDone
    }
    case None => {
      nextFunction
      !isDone
    }
  }

  private def isDone = function == None

  private def reportError = {
    errors = function.get::errors
    nextFunction
  }

  private def reportUnknown = {
    nextModel
    if (model == None) {
      unknowns = function.get::unknowns
      nextFunction
    }
  }

  private def reportValid = {
    clusters = clusters + (model.get -> (function.get::clusters(model.get)))

    nextFunction
  }

  private def reportWrong = {
    trace = None
    wrong = function.get::wrong
  }

}