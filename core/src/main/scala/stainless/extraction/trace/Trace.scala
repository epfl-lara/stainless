/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package trace

import stainless.utils.CheckFilter

class Trace(override val s: Trees, override val t: termination.Trees)
           (using override val context: inox.Context)
  extends CachingPhase
     with IdentityFunctions
     with IdentitySorts { self =>
  import s._

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  private[this] class Identity(override val s: self.s.type, override val t: self.t.type) extends transformers.ConcreteTreeTransformer(s, t)
  private[this] val identity = new Identity(self.s, self.t)

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    import symbols.{given, _}
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
        })

        val res = s.ValDef.fresh("res", s.UnitType())
        val cond = s.Equals(s.FunctionInvocation(fd1.id, newParamTps, newParamVars), s.FunctionInvocation(fd2.id, newParamTps, newParamVars))
        val post = Postcondition(Lambda(Seq(res), cond))

        val withPre = exprOps.reconstructSpecs(pre, Some(body), s.UnitType())
        val fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed

        val flags: Seq[s.Flag] = Seq(s.Derived(Some(fd1.id)), s.Annotation("traceInduct",List(StringLiteral(fd1.id.name))))

        new s.FunDef(id, newParamTypes, newParams, returnType, fullBody, flags)
      }

      (Trace.getModel, Trace.getFunction) match {
        case (Some(model), Some(function)) => {
          val m = symbols.functions(model)
          val f = symbols.functions(function)
          if (m.params.size == f.params.size) {
            val newFun = equivalenceChek(m, f)
            Some(newFun)
          }
          else {
            Trace.resetTrace
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
          BodyWithSpecs(fd.fullBody).getSpec(PostconditionKind) match {
            case Some(Postcondition(post)) => 
              s.exprOps.preTraversal {
                case _ if funInv.isDefined => // do nothing
                case fi @ s.FunctionInvocation(tfd, _, args) if symbols.isRecursive(tfd) && (fun.contains(StringLiteral(tfd.name)) || fun.contains(StringLiteral("")))
                => {
                      val paramVars = fd.params.map(_.toVariable)
                      val argCheck = args.forall(paramVars.contains) && args.toSet.size == args.size
                      if (argCheck) funInv = Some(fi)
                    }
                case _ => 
              }(post)
            case _ => 
          }
        }
      }

      funInv match {
        case Some(finv) => {
          // make a helper lemma:
          val helper = inductPattern(symbols, symbols.functions(finv.id), fd).setPos(fd.getPos)

          // transform the main lemma
          val proof = FunctionInvocation(helper.id, fd.tparams.map(_.tp), fd.params.map(_.toVariable))
          val body = Let(s.ValDef.fresh("ind$proof", helper.returnType), proof, exprOps.withoutSpecs(fd.fullBody).get)
          val withPre = exprOps.reconstructSpecs(BodyWithSpecs(fd.fullBody).specs, Some(body), fd.returnType)
          val lemma = fd.copy(
            fullBody = BodyWithSpecs(withPre).reconstructed,
            flags = (s.Derived(Some(fd.id)) +: s.Derived(Some(finv.id)) +: (fd.flags.filterNot(f => f.name == "traceInduct"))).distinct
          ).copiedFrom(fd).setPos(fd.getPos)

          Trace.setTrace(lemma.id)
          Trace.setProof(helper.id)
          List(helper, lemma)
        }
        case None => {
          val lemma = fd.copy(
            flags = (s.Derived(Some(fd.id)) +: (fd.flags.filterNot(f => f.name == "traceInduct")))
          ).copiedFrom(fd).setPos(fd.getPos)
          Trace.setTrace(lemma.id)
          List(lemma)
        }
      }
    } else List())

    val extractedSymbols = super.extractSymbols(context, symbols)
    
    val extracted = t.NoSymbols
      .withSorts(extractedSymbols.sorts.values.toSeq)
      .withFunctions(extractedSymbols.functions.values.filterNot(fd => fd.flags.exists(elem => elem.name == "traceInduct")).toSeq)

    registerFunctions(extracted, inductFuns.map(fun => identity.transform(fun)))
  }

  def inductPattern(symbols: s.Symbols, model: FunDef, lemma: FunDef) = {
    import symbols.{given, _}
    import exprOps._

    val id = FreshIdentifier(s"${lemma.id}$$induct")

    val newParams = model.params.map{param => param.freshen}
    val newParamVars = newParams.map{param => param.toVariable}
    val newParamTypes = model.tparams.map{tparam => tparam.freshen}
    val newParamTps = newParamTypes.map{tparam => tparam.tp}

    val returnType = model.returnType
    val flags = Seq(s.Derived(Some(lemma.id)), s.Derived(Some(model.id)))

    val body = FunctionInvocation(model.id, newParamTps, newParamVars)
    val indPattern = new s.FunDef(id, newParamTypes, newParams, returnType, body, flags)

    val fi = FunctionInvocation(model.id, newParamTps, newParamVars)

    class Specializer(
      origFd: FunDef,
      newId: Identifier,
      vsubst: Map[Identifier, Expr]
    ) extends s.ConcreteStainlessSelfTreeTransformer { speSelf =>

      override def transform(expr: speSelf.s.Expr): speSelf.t.Expr = expr match {
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
      case s => context.reporter.fatalError(s"Unsupported specs: $s")
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

  private lazy val pathsOptModels: Option[Seq[Path]] = context.options.findOption(optModels) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  private def shouldBeChecked(fid: Identifier): Boolean = shouldBeChecked(pathsOpt, fid)
  private def isModel(fid: Identifier): Boolean = shouldBeChecked(pathsOptModels, fid)

  private def shouldBeChecked(paths: Option[Seq[Path]], fid: Identifier): Boolean = paths match {
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

  def optionsError(using ctx: inox.Context): Boolean =
    !ctx.options.findOptionOrDefault(frontend.optBatchedProgram) && 
    (!ctx.options.findOptionOrDefault(optModels).isEmpty || !ctx.options.findOptionOrDefault(optCompareFuns).isEmpty)
        
  def printEverything(using ctx: inox.Context) = {
    import ctx.{ reporter, timers }
    if (!clusters.isEmpty || !errors.isEmpty || !unknowns.isEmpty || !wrong.isEmpty) {
      reporter.info(s"Printing equivalence checking results:")  
      allModels.foreach(model => {
        val l = clusters(model).map(CheckFilter.fixedFullName).mkString(", ")
        val m = CheckFilter.fixedFullName(model)
        reporter.info(s"List of functions that are equivalent to model $m: $l")
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
  var trace: Option[Identifier] = None
  var proof: Option[Identifier] = None

  def apply(ts: Trees, tt: termination.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends Trace(s, t)
    new Impl(ts, tt)
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

  def setTrace(t: Identifier) = trace = Some(t)
  def setProof(p: Identifier) = proof = Some(p)


  def resetTrace = {
    trace = None
    proof = None
  }

  //iterate model for the current function
  def nextModel = tmpModels match {
    case x::xs => { 
      tmpModels = xs
      model = Some(x)
    }
    case Nil => model = None
  }

  //iterate function to check; reset model
  def nextFunction = {
    trace = None
    proof = None
      tmpFunctions match {
      case x::xs => {
        tmpModels = allModels
        nextModel
        tmpFunctions = xs
        function = Some(x)
      }
      case Nil => {
        function = None
      }
    }
  }

  def nextIteration[T <: AbstractReport[T]](report: AbstractReport[T])(using inox.Context): Boolean = {
    (function, proof, trace) match {
      case (Some(f), Some(p), Some(t)) => {
        if (report.hasError(f) || report.hasError(p) || report.hasError(t)) reportError
        else if (report.hasUnknown(f) || report.hasUnknown(p) || report.hasError(t)) reportUnknown
        else reportValid
      }
      case (Some(f), _, Some(t)) => {
        if (report.hasError(f) || report.hasError(t)) reportError
        else if (report.hasUnknown(f) || report.hasError(t)) reportUnknown
        else reportValid
      }
      case _ => reportWrong
    }
    !isDone
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
    if (function != None) wrong = function.get::wrong
    resetTrace
    nextFunction
  }

}