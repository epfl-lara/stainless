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

    if (Trace.getNorm.isEmpty) {
      val normOpt = symbols.functions.values.toList.find(elem => isNorm(elem.id)).map(elem => elem.id)

      def checkArgs(model: Identifier, norm: Identifier) = {
        val m = symbols.functions(model)
        val n = symbols.functions(norm)

        n.params.size >= 1 && n.params.init.size == m.params.size && n.tparams.size == m.tparams.size
      }

      (Trace.getModel, normOpt) match {
        case (Some(model), Some(norm)) if checkArgs(model, norm) =>
          Trace.setNorm(normOpt)
        case _ =>
      }
    }

    def generateEqLemma: Option[s.FunDef] = {
      def equivalenceChek(fd1: s.FunDef, fd2: s.FunDef): s.FunDef = {
        val freshId = FreshIdentifier(CheckFilter.fixedFullName(fd1.id) + "$" + CheckFilter.fixedFullName(fd2.id))
        val eqLemma = exprOps.freshenSignature(fd1).copy(id = freshId)
        
        val newParamTps = eqLemma.tparams.map{tparam => tparam.tp}
        val newParamVars = eqLemma.params.map{param => param.toVariable}

        val subst = (fd1.params.map(_.id) zip newParamVars).toMap
        val tsubst = (fd1.tparams zip newParamTps).map { case (tparam, targ) => tparam.tp.id -> targ }.toMap
        val specializer = new Specializer(eqLemma, eqLemma.id, tsubst, subst)

        val specs = BodyWithSpecs(fd1.fullBody).specs.filter(s => s.kind == LetKind || s.kind == PreconditionKind) 
        val pre = specs.map(spec => spec match {
          case Precondition(cond) => Precondition(specializer.transform(cond))
          case LetInSpec(vd, expr) => LetInSpec(vd, specializer.transform(expr))
        })

        val fun1 = s.FunctionInvocation(fd1.id, newParamTps, newParamVars)
        val fun2 = s.FunctionInvocation(fd2.id, newParamTps, newParamVars)

        val (normFun1, normFun2) = Trace.getNorm match {
          case Some(n) => (
            s.FunctionInvocation(n, newParamTps, newParamVars :+ fun1), 
            s.FunctionInvocation(n, newParamTps, newParamVars :+ fun2))
          case None => (fun1, fun2)
        }

        val res = s.ValDef.fresh("res", s.UnitType())
        val cond = s.Equals(normFun1, normFun2)
        val post = Postcondition(Lambda(Seq(res), cond))

        val body = s.UnitLiteral()
        val withPre = exprOps.reconstructSpecs(pre, Some(body), s.UnitType())

        eqLemma.copy(
          fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed,
          flags = Seq(s.Derived(Some(fd1.id)), s.Annotation("traceInduct",List(StringLiteral(fd1.id.name)))),
          returnType = s.UnitType()
        ).copiedFrom(eqLemma)
      }

      (Trace.getModel, Trace.getFunction) match {
        case (Some(model), Some(function)) => {
          val m = symbols.functions(model)
          val f = symbols.functions(function)
          if (m.params.size == f.params.size)
            Some(equivalenceChek(m, f))
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
                case fi @ s.FunctionInvocation(tfd, tps, args) if symbols.isRecursive(tfd) && (fun.contains(StringLiteral(tfd.name)) || fun.contains(StringLiteral("")))
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
          val proof = FunctionInvocation(helper.id, finv.tps, fd.params.map(_.toVariable))
          val returnType = typeOps.instantiateType(helper.returnType, (helper.typeArgs zip fd.typeArgs).toMap)

          val body = Let(s.ValDef.fresh("ind$proof", returnType), proof, exprOps.withoutSpecs(fd.fullBody).get)
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
    import symbols._
    import exprOps._

    val indPattern = exprOps.freshenSignature(model).copy(id = FreshIdentifier(lemma.id+"$induct"))
    val newParamTps = indPattern.tparams.map{tparam => tparam.tp}
    val newParamVars = indPattern.params.map{param => param.toVariable}

    val fi = FunctionInvocation(model.id, newParamTps, newParamVars)

    val tpairs = model.tparams zip fi.tps
    val tsubst = tpairs.map { case (tparam, targ) => tparam.tp.id -> targ } .toMap
    val subst = (model.params.map(_.id) zip fi.args).toMap
    val specializer = new Specializer(model, indPattern.id, tsubst, subst)
    
    val fullBodySpecialized = specializer.transform(exprOps.withoutSpecs(model.fullBody).get)

    val specsSubst = (lemma.params.map(_.id) zip newParamVars).toMap ++ (model.params.map(_.id) zip newParamVars).toMap
    val specsTsubst = ((lemma.tparams zip fi.tps) ++ (model.tparams zip fi.tps)).map { case (tparam, targ) => tparam.tp.id -> targ }.toMap
    val specsSpecializer = new Specializer(indPattern, indPattern.id, specsTsubst, specsSubst)

    val specs = BodyWithSpecs(model.fullBody).specs ++ BodyWithSpecs(lemma.fullBody).specs.filterNot(_.kind == MeasureKind)
    val pre = specs.filterNot(_.kind == PostconditionKind).map(spec => spec match {
      case Precondition(cond) => Precondition(specsSpecializer.transform(cond)).setPos(spec)
      case LetInSpec(vd, expr) => LetInSpec(vd, specsSpecializer.transform(expr)).setPos(spec)
      case Measure(measure) => Measure(specsSpecializer.transform(measure)).setPos(spec)
      case s => context.reporter.fatalError(s"Unsupported specs: $s")
    })

    val withPre = exprOps.reconstructSpecs(pre, Some(fullBodySpecialized), indPattern.returnType)

    val speccedLemma = BodyWithSpecs(lemma.fullBody).addPost
    val speccedOrig = BodyWithSpecs(model.fullBody).addPost
    val postLemma = speccedLemma.getSpec(PostconditionKind).map(post => 
      specsSpecializer.transform(post.expr))
    val postOrig = speccedOrig.getSpec(PostconditionKind).map(post => specsSpecializer.transform(post.expr))
    
    (postLemma, postOrig) match {
      case (Some(Lambda(Seq(res1), cond1)), Some(Lambda(Seq(res2), cond2))) => 
        val res = ValDef.fresh("res", indPattern.returnType)
        val freshCond1 = exprOps.replaceFromSymbols(Map(res1 -> res.toVariable), cond1)
        val freshCond2 = exprOps.replaceFromSymbols(Map(res2 -> res.toVariable), cond2)

        val cond = andJoin(Seq(freshCond1, freshCond2))
        val post = Postcondition(Lambda(Seq(res), cond))

        indPattern.copy(
          fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed,
          flags = Seq(s.Derived(Some(lemma.id)), s.Derived(Some(model.id)))
        ).copiedFrom(indPattern)
    }

  }

  class Specializer(
      origFd: FunDef,
      newId: Identifier,
      tsubst: Map[Identifier, Type],
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

      override def transform(tpe: s.Type): t.Type = tpe match {
        case tp: TypeParameter =>
          tsubst.getOrElse(tp.id, super.transform(tp))

        case _ => super.transform(tpe)
      }
    }

  type Path = Seq[String]

  private lazy val pathsOpt: Option[Seq[Path]] = context.options.findOption(optCompareFuns) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  private lazy val pathsOptModels: Option[Seq[Path]] = context.options.findOption(optModels) map { functions =>
    functions map CheckFilter.fullNameToPath
  }

  private lazy val pathsOptNorm: Option[Seq[Path]] = 
    Some(Seq(context.options.findOptionOrDefault(optNorm)).map(CheckFilter.fullNameToPath))

  private def shouldBeChecked(fid: Identifier): Boolean = shouldBeChecked(pathsOpt, fid)
  private def isModel(fid: Identifier): Boolean = shouldBeChecked(pathsOptModels, fid)
  private def isNorm(fid: Identifier): Boolean = shouldBeChecked(pathsOptNorm, fid)

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

  object Status extends Enumeration {
    type Status = Value
    val Valid, Unknown, Errorneus, Wrong = Value
  }

  import Status._

  case class State(var status: Status, var path: List[Identifier])

  var state: Map[Identifier, State] = Map()

  def optionsError(implicit ctx: inox.Context): Boolean = 
    !ctx.options.findOptionOrDefault(frontend.optBatchedProgram) && 
    (!ctx.options.findOptionOrDefault(optModels).isEmpty || !ctx.options.findOptionOrDefault(optCompareFuns).isEmpty)
      
  def printEverything(implicit ctx: inox.Context) = {
    import ctx.{ reporter, timers }
    if(!clusters.isEmpty || !errors.isEmpty || !unknowns.isEmpty || !wrong.isEmpty) {
      reporter.info(s"Printing equivalence checking results:")  
      allModels.foreach(model => if (!clusters(model).isEmpty) {
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

      reporter.info(s"Printing the final state:")  
      allFunctions.foreach(f => {
        val l = state(f).path.map(CheckFilter.fixedFullName).mkString(", ")
        val m = CheckFilter.fixedFullName(f)
        reporter.info(s"Path for the function $m: $l")
      })
    }

  }

  var allModels: List[Identifier] = List()
  var tmpModels: List[Identifier] = List()

  var allFunctions: List[Identifier] = List()
  var tmpFunctions: List[Identifier] = List()

  var model: Option[Identifier] = None
  var function: Option[Identifier] = None
  var norm: Option[Identifier] = None
  var trace: Option[Identifier] = None
  var proof: Option[Identifier] = None

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
    state = state ++ (m zip m.map(_ => State(Valid, List()))).toMap
  }

  def setFunctions(f: List[Identifier]) = {
    allFunctions = f
    tmpFunctions = f
    state = state ++ (f zip f.map(_ => State(Unknown, List()))).toMap
  }

  def getModels = allModels

  def getFunctions = allFunctions

  //model for the current iteration
  def getModel = model

  //function to check in the current iteration
  def getFunction = function

  def getNorm = norm

  def setTrace(t: Identifier) = trace = Some(t)
  def setProof(p: Identifier) = proof = Some(p)

  def setNorm(n: Option[Identifier]) = norm = n

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

  def nextIteration[T <: AbstractReport[T]](report: AbstractReport[T])(implicit context: inox.Context): Boolean = {
    (function, proof, trace) match {
      case (Some(f), Some(p), Some(t)) => {
        if (report.hasError(f) || report.hasError(p) || report.hasError(t)) reportError
        else if (report.hasUnknown(f) || report.hasUnknown(p) || report.hasUnknown(t)) reportUnknown
        else reportValid
      }
      case (Some(f), _, Some(t)) => {
        if (report.hasError(f) || report.hasError(t)) reportError
        else if (report.hasUnknown(f) || report.hasUnknown(t)) reportUnknown
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
    if (!allModels.contains(function.get)) {
      state(function.get).status = Valid
      state(function.get).path = model.get +: state(model.get).path
      allModels = allModels :+ function.get
      clusters = clusters + (function.get -> List())
    }

    clusters = clusters + (model.get -> (function.get::clusters.getOrElse(model.get, List())))

    nextFunction
  }

  private def reportWrong = {
    if (function != None) wrong = function.get::wrong
    resetTrace
    nextFunction
  }

}