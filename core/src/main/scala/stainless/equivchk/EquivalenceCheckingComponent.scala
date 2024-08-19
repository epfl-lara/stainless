package stainless
package equivchk

import inox.Context
import io.circe.Json
import stainless.extraction._
import stainless.extraction.xlang.{trees => xt}
import stainless.termination.MeasureInference
import stainless.utils.{CheckFilter, JsonUtils}
import stainless.verification._

import java.io.File
import scala.concurrent.Future

object DebugSectionEquivChk extends inox.DebugSection("equivchk")

object optCompareFuns extends inox.OptionDef[Seq[String]] {
  val name = "comparefuns"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

object optModels extends inox.OptionDef[Seq[String]] {
  val name = "models"
  val default = Seq[String]()
  val parser = inox.OptionParsers.seqParser(inox.OptionParsers.stringParser)
  val usageRhs = "f1,f2,..."
}

object optNorm extends inox.StringOptionDef("norm", "", "f")

object optEquivalenceOutput extends FileOptionDef {
  val name = "equivchk-output"
  val default = new File("equivchk-output.json")
}

object optN extends inox.IntOptionDef("equivchk-n", EquivalenceChecker.defaultN, "<int>")
object optInitScore extends inox.IntOptionDef("equivchk-init-score", EquivalenceChecker.defaultInitScore, "<int>")
object optInitWeights extends inox.OptionDef[Map[String, Int]] {
  val name = "equivchk-init-weights"
  val default = Map.empty
  val parser = s => {
    def tryParsePair(s: String): Option[(String, Int)] = {
      val ix = s.lastIndexOf(':')
      if (ix <= 0) None // Also exclude empty function name
      else {
        val (fn, w) = s.splitAt(ix)
        w.drop(1).toIntOption.map(fn -> _)
      }
    }
    val pairs = s.split(",")

    def go(i: Int, acc: Map[String, Int]): Option[Map[String, Int]] = {
      if (i >= pairs.length) Some(acc)
      else tryParsePair(pairs(i)) match {
        case Some(p) => go(i + 1, acc + p)
        case None => None
      }
    }
    go(0, Map.empty)
  }
  val usageRhs = "fn1:w1,fn2:w2,..."
}
object optMaxPerm extends inox.IntOptionDef("equivchk-max-perm", EquivalenceChecker.defaultMaxMatchingPermutation, "<int>")
object optMaxCtex extends inox.IntOptionDef("equivchk-max-ctex", EquivalenceChecker.defaultMaxCtex, "<int>")
object optMeasureTransfer extends inox.FlagOptionDef("equivchk-transfer", false)

object EquivalenceCheckingComponent extends Component {
  override val name = "equivchk"
  override val description = "Equivalence checking of functions"

  override type Report = EquivalenceCheckingReport
  override type Analysis = EquivalenceCheckingAnalysis

  override val lowering = {
    class LoweringImpl(override val s: trees.type, override val t: trees.type)
      extends transformers.ConcreteTreeTransformer(s, t)
    inox.transformers.SymbolTransformer(new LoweringImpl(trees, trees))
  }

  override def run(pipeline: StainlessPipeline)(using inox.Context): EquivalenceCheckingRun = {
    new EquivalenceCheckingRun(pipeline)
  }
}

class EquivalenceCheckingRun private(override val component: EquivalenceCheckingComponent.type,
                                     override val trees: stainless.trees.type,
                                     override val pipeline: StainlessPipeline, // unused - we have our own
                                     val underlyingRun: VerificationRun)
                                    (using override val context: inox.Context) extends ComponentRun { self =>
  import EquivalenceCheckingReport._
  def this(pipeline: StainlessPipeline)(using inox.Context) =
    this(EquivalenceCheckingComponent, stainless.trees, pipeline, new VerificationRun(pipeline))

  import component.{Analysis, Report}
  import extraction.given

  override def parse(json: Json): Report = ???

  override def createPipeline = underlyingRun.createPipeline
  given givenDebugSection: DebugSectionEquivChk.type = DebugSectionEquivChk

  private val tracePrePipeline: ExtractionPipeline { val s: xlang.trees.type; val t: trace.trees.type } =
    xlang.extractor andThen
    innerclasses.extractor andThen
    methods.extractor andThen
    throwing.extractor andThen
    imperative.extractor andThen
    oo.extractor andThen
    innerfuns.extractor andThen
    inlining.extractor

  private val tracePostPipeline: ExtractionPipeline { val s: trace.trees.type; val t: trees.type } =
    trace.extractor andThen
    termination.extractor andThen
    extraction.utils.NamedPipeline("MeasureInference", MeasureInference(extraction.trees)) andThen
    extraction.utils.NamedPipeline("PartialEvaluation", PartialEvaluation(extraction.trees)) andThen
    extraction.completer(trees)

  override def apply(ids: Seq[Identifier], symbols: xt.Symbols): Future[Analysis] = {
    val (traceSyms, traceSummary) = tracePrePipeline.extract(symbols)
    val (plainSyms, plainSummary) = tracePostPipeline.extract(traceSyms)
    val ec = EquivalenceChecker.tryCreate(trace.trees)(traceSyms) match {
      case fail: EquivalenceChecker.Creation.Failure => explainAndSayFarewell(fail.reason)
      case success: EquivalenceChecker.Creation.Success => success.equivChker
    }
    val toProcess = createFilter.filter(ids, plainSyms, underlyingRun.component)
    val underlyingRun1 = new VerificationRun(pipeline)(using context.withOpts(stainless.termination.optCheckMeasures(stainless.utils.YesNoOnly.No),stainless.termination.optInferMeasures(false)))
    for {
      gen <- underlyingRun1.execute(toProcess, plainSyms, ExtractionSummary.Node(traceSummary, plainSummary))
      invalidVCsCands = counterExamples(gen).flatMap {
        case (vc, ctex) => ec.reportUnsafe(gen.program)(gen, vc, ctex).getOrElse(Set.empty)
      }.toSeq.distinct
      unknownsSafetyCands = unknowns(gen).flatMap(ec.reportUnknown(gen.program)(gen, _).getOrElse(Set.empty)).toSeq.distinct
      _ = debugInvalidVCsCandidates(invalidVCsCands)
      _ = debugUnknownsSafetyCandidates(unknownsSafetyCands)
      trRes <- equivCheck(ec)
    } yield buildAnalysis(ec)(ids, gen, trRes)
  }

  private def buildAnalysis(ec: EquivalenceChecker)(ids: Seq[Identifier], general: VerificationAnalysis, trRes: ec.Results): EquivalenceCheckingAnalysis = {
    val genRecors = general.toReport.results.map { verifRecord =>
      Record(verifRecord.id, verifRecord.pos, verifRecord.time, Status.Verification(verifRecord.status), verifRecord.solverName, verifRecord.kind, verifRecord.derivedFrom)
    }
    val valid = trRes.valid.toSeq.sortBy(_._1).map {
      case (v, data) =>
        assert(data.path.nonEmpty)
        val fd = ec.symbols.getFunction(v)
        val directModel = data.path.head
        Record(v, fd.getPos, data.solvingInfo.time,
          Status.Equivalence(EquivalenceStatus.Valid(directModel, data.solvingInfo.fromCache, data.solvingInfo.trivial)),
          data.solvingInfo.solverName, "equivalence", fd.source)
    }
    val unequiv = trRes.unequivalent.toSeq.sortBy(_._1).flatMap {
      case (errn, ec.UnequivalentData(_, solvingInfo)) =>
        val fd = ec.symbols.getFunction(errn)
        Some(Record(errn, fd.getPos, solvingInfo.map(_.time).getOrElse(0L),
          Status.Equivalence(EquivalenceStatus.Unequivalent),
          solvingInfo.flatMap(_.solverName), "equivalence", fd.source))
    }
    val unsafe = trRes.unsafe.toSeq.sortBy(_._1).flatMap {
      case (errn, _) =>
        val fd = ec.symbols.getFunction(errn)
        Some(Record(errn, fd.getPos, 0L,
          Status.Equivalence(EquivalenceStatus.Unsafe),
          None, "safety", fd.source))
    }
    val unknwsSafety = trRes.unknownsSafety.toSeq.sortBy(_._1).flatMap {
      case (fnId, _) =>
        val fd = ec.symbols.getFunction(fnId)
        Some(Record(fnId, fd.getPos, 0L,
          Status.Equivalence(EquivalenceStatus.UnknownSafety),
          None, "safety", fd.source))
    }
    val wrgs = trRes.wrongs.toSeq.sorted.map { wrong =>
      val fd = ec.symbols.getFunction(wrong)
      // No solver or time specified because it's a signature mismatch
      Record(wrong, fd.getPos, 0L, Status.Equivalence(EquivalenceStatus.Wrong), None, "equivalence", fd.source)
    }
    val unknwsEquiv = trRes.unknownsEquivalence.toSeq.sortBy(_._1).map {
      case (unknown, data) =>
        val fd = ec.symbols.getFunction(unknown)
        Record(unknown, fd.getPos, data.solvingInfo.time, Status.Equivalence(EquivalenceStatus.UnknownEquivalence), data.solvingInfo.solverName, "equivalence", fd.source)
    }

    val allRecords = genRecors ++ valid ++ unsafe ++ unequiv ++ wrgs ++ unknwsSafety ++ unknwsEquiv
    new EquivalenceCheckingAnalysis(ids.toSet, allRecords, general.extractionSummary)
  }

  private def equivCheck(ec: EquivalenceChecker): Future[ec.Results] = {
    class Identity(override val s: ec.trees.type, override val t: trace.trees.type) extends transformers.ConcreteTreeTransformer(s, t)
    val identity = new Identity(ec.trees, trace.trees)

    def examination(): Future[ec.Results] = {
      ec.pickNextExamination() match {
        case ec.NextExamination.Done(pruned, res) =>
          debugPruned(ec)(pruned)
          printResults(ec)(res)
          context.options.findOption(equivchk.optEquivalenceOutput) match {
            case Some(out) => dumpResultsJson(out, ec)(res)
            case None => ()
          }
          Future.successful(res)
        case ec.NextExamination.NewCandidate(cand, model, strat, pruned) =>
          debugPruned(ec)(pruned)
          debugNewCandidate(ec)(cand, model, strat)
          round()
      }
    }

    def round(): Future[ec.Results] = {
      val generated = ec.prepareRound()
      val allFns = (ec.symbols.functions -- generated.map(_.id)).values.toSeq ++ generated
      val syms: trace.trees.Symbols = trace.trees.NoSymbols
        .withSorts(ec.symbols.sorts.values.map(identity.transform).toSeq)
        .withFunctions(allFns.map(identity.transform))
      // here, termination is checked for the generated functions
      // the result is simply stored in the equivalence entry in the summary table
      // generated functions include candidate program with decreases
      // println(generated)
      val plainSyms = tracePostPipeline.extract(syms)._1
      underlyingRun.execute(generated.map(_.id), plainSyms, ExtractionSummary.NoSummary)
        .flatMap { analysis =>
          val concl = ec.concludeRound(analysis)
          concl match {
            case ec.RoundConclusion.NextRound(cand, model, strat, prunedSubFnsPairs) =>
              debugNewRound(ec)(cand, model, strat)
              debugPrunedSubFnsPairs(prunedSubFnsPairs)
              round()
            case ec.RoundConclusion.CandidateClassified(cand, classification, prunedSubFnsPairs) =>
              debugClassified(ec)(cand, classification)
              debugPrunedSubFnsPairs(prunedSubFnsPairs)
              examination()
          }
        }
    }

    examination()
  }

  private def counterExamples(analysis: VerificationAnalysis) = {
    analysis.vrs.collect {
      case (vc, VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), _, _, _)) =>
        vc -> model
    }.toMap
  }

  private def unknowns(analysis: VerificationAnalysis) = {
    analysis.vrs.collect {
      case (vc, vcRes) if vcRes.isInconclusive => vc
    }
  }

  private def debugInvalidVCsCandidates(cands: Seq[Identifier]): Unit = {
    if (cands.nonEmpty) {
      context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
        debug(s"The following candidates were pruned for having invalid VCs:")
        val candsStr = cands.sorted.map(_.fullName).mkString("  ", "\n  ", "")
        debug(candsStr)
      }
    }
  }

  private def debugUnknownsSafetyCandidates(cands: Seq[Identifier]): Unit = {
    if (cands.nonEmpty) {
      context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
        debug(s"The following candidates were pruned for having unknowns VCs:")
        val candsStr = cands.sorted.map(_.fullName).mkString("  ", "\n  ", "")
        debug(candsStr)
      }
    }
  }

  private def debugPruned(ec: EquivalenceChecker)(pruned: Map[Identifier, ec.PruningReason]): Unit = {
    def pretty(fn: Identifier, reason: ec.PruningReason): Seq[String] = {
      val rsonStr = reason match {
        case ec.PruningReason.SignatureMismatch => Seq("signature mismatch")
        case ec.PruningReason.ByTest(testId, sampleIx, ctex) =>
          Seq(s"test falsification by ${testId.fullName} sample n°${sampleIx + 1}:") ++ prettyCtex(ec)(ctex).map("  " ++ _) // add 2 indentation
        case ec.PruningReason.ByPreviousCtex(ctex) =>
          Seq(s"counter-example falsification:") ++ prettyCtex(ec)(ctex).map("  " ++ _)
      }
      Seq(s"${fn.fullName}:") ++ rsonStr.map("  " ++ _)
    }

    if (pruned.nonEmpty) {
      context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
        debug("The following functions were pruned:")
        val lines = pruned.toSeq.sortBy(_._1).flatMap(pretty.tupled)
        lines.foreach(s => debug(s"  $s"))
      }
    }
  }

  private def debugNewCandidate(ec: EquivalenceChecker)(cand: Identifier, model: Identifier, strat: ec.EquivCheckStrategy): Unit = {
    context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
      debug(s"Picking new candidate: ${cand.fullName} with model ${model.fullName} and strategy ${strat.pretty}")
    }
  }

  private def debugNewRound(ec: EquivalenceChecker)(cand: Identifier, model: Identifier, strat: ec.EquivCheckStrategy): Unit = {
    context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
      debug(s"Retry for ${cand.fullName} with model ${model.fullName} and strategy: ${strat.pretty}")
    }
  }

  private def debugClassified(ec: EquivalenceChecker)(cand: Identifier, classification: ec.Classification): Unit = {
    context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
      val msg = classification match {
        case ec.Classification.Valid(model) => s"valid whose direct model is ${model.fullName}"
        case ec.Classification.Invalid(ctexs) =>
          val ctexStr = ctexs.flatMap(prettyCtex(ec)(_)).map(s => s"  $s").mkString("\n  ")
          s"invalid with the following counter-examples:\n  $ctexStr"
        case ec.Classification.Unknown => "unknown"
      }
      debug(s"${cand.fullName} is $msg")
    }
  }

  private def debugPrunedSubFnsPairs(prunedSubFnsPairs: Set[(Identifier, Identifier, EquivalenceChecker.ArgPermutation)]): Unit = {
    if (prunedSubFnsPairs.nonEmpty) {
      context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
        val str = prunedSubFnsPairs.toSeq.map { case (mod, cand, perm) => (mod.fullName, cand.fullName, perm) }.sortBy(_._1)
          .map { case (mod, cand, perm) => s"$mod <-> $cand (permutation = ${perm.m2c.mkString(", ")})" }
          .mkString(", ")
        debug(s"(pruned all matching containing the following subfns pairs: $str)")
      }
    }
  }

  private def printResults(ec: EquivalenceChecker)(res: ec.Results): Unit = {
    import context.reporter.info

    info("Printing equivalence checking results:")
    res.equiv.foreach { case (m, l) =>
      val lStr = l.map(_.fullName)
      info(s"List of functions that are equivalent to model ${m.fullName}: ${lStr.mkString(", ")}")
    }
    val errns = res.unequivalent.keys.toSeq.map(_.fullName).sorted.mkString(", ")
    val unknownsSafety = res.unknownsSafety.keys.toSeq.map(_.fullName).sorted.mkString(", ")
    val unknownsEquiv = res.unknownsEquivalence.keys.toSeq.map(_.fullName).sorted.mkString(", ")
    val wrongs = res.wrongs.toSeq.map(_.fullName).sorted.mkString(", ")
    info(s"List of erroneous functions: $errns")
    info(s"List of timed-out functions (safety): $unknownsSafety")
    info(s"List of timed-out functions (equivalence): $unknownsEquiv")
    info(s"List of wrong functions: $wrongs")
    info(s"Printing the final state:")
    res.valid.foreach { case (cand, data) =>
      val pathStr = data.path.map(_.fullName).mkString(", ")
      info(s"Path for the function ${cand.fullName}: $pathStr")
    }
    res.unequivalent.foreach { case (cand, data) =>
        val ctexsStr = data.ctexs.flatMap(prettyCtex(ec)(_))
        info(s"Unequivalence counterexample for the function ${cand.fullName}:")
        ctexsStr.foreach(s => info(s"  $s"))
    }

    def unsafeCtexStr(data: ec.UnsafeCtex): String = {
      val ctexsStr = data.ctex.map(ctex => ctex.map { case (vd, arg) => s"${vd.id.name} -> $arg" }.mkString(", "))
        .getOrElse("(could not extract counter-examples)")
      s"${data.kind.name} @ ${data.pos.line}:${data.pos.col}: $ctexsStr"
    }
    res.unsafe.foreach { case (cand, data) =>
      info(s"Unsafety for the function ${cand.fullName}")
      if (data.self.nonEmpty) {
        info(s"  Direct unsafety:")
        data.self.foreach(ctex => info(s"    ${unsafeCtexStr(ctex)}"))
      }
      data.auxiliaries.toSeq.sortBy(_._1.fullName).foreach { (aux, ctexs) =>
        info(s"  Transitive unsafety by calling ${aux.fullName}:")
        ctexs.foreach(ctex => info(s"    ${unsafeCtexStr(ctex)}"))
      }
    }
  }

  // This returns a Seq due to being multiline and to allow easier indentation
  private def prettyCtex(ec: EquivalenceChecker)(ctex: ec.Ctex): Seq[String] = {
    val args = ctex.mapping.map { case (vd, e) => s"${vd.id.name} -> $e" }.mkString(", ")
    val eval = ctex.eval.map(ev => Seq(s"Expected ${ev.expected} but got ${ev.got}")).getOrElse(Seq.empty)
    Seq(args) ++ eval
  }

  private def dumpResultsJson(out: File, ec: EquivalenceChecker)(res: ec.Results): Unit = {
    def ctexJson(ctex: ec.Ctex): Json = {
      val args = Json.fromFields(ctex.mapping.map { case (vd, expr) => vd.id.name -> Json.fromString(expr.toString) })
      Json.fromFields(
        Seq("args" -> args) ++
        ctex.eval.map(ev => Seq(
          "expected" -> Json.fromString(ev.expected.toString),
          "got" -> Json.fromString(ev.got.toString)
        )).getOrElse(Seq.empty)
      )
    }

    def unsafeCtexJson(data: ec.UnsafeCtex): Json = Json.fromFields(Seq(
      "kind" -> Json.fromString(data.kind.name),
      "position" -> Json.fromString(s"${data.pos.line}:${data.pos.col}"),
      "ctex" -> data.ctex.map(mapping => ctexJson(ec.Ctex(mapping, None))).getOrElse(Json.Null)
    ))
    def unknownVCJson(data: ec.UnknownSafetyVC): Json = Json.fromFields(Seq(
      "kind" -> Json.fromString(data.kind.name),
      "position" -> Json.fromString(s"${data.pos.line}:${data.pos.col}"),
    ))

    val equivs = res.equiv.map { case (m, l) => m.fullName -> l.map(_.fullName).toSeq.sorted }
      .toSeq.sortBy(_._1)
    val unknownsEquiv = res.unknownsEquivalence.keys.toSeq.map(_.fullName).sorted
    val wrongs = res.wrongs.toSeq.map(_.fullName).sorted
    val weights = res.weights.map { case (mod, w) => mod.fullName -> w }.toSeq
      .sortBy { case (mod, w) => (-w, mod) }

    val json = Json.fromFields(Seq(
      "equivalent" -> Json.fromValues(equivs.map { case (m, l) =>
        Json.fromFields(Seq(
          "model" -> Json.fromString(m),
          "functions" -> Json.fromValues(l.map(Json.fromString))
        ))
      }),
      "unequivalent" -> Json.fromValues(res.unequivalent.toSeq.sortBy(_._1).map { case (cand, data) =>
        Json.fromFields(Seq(
          "function" -> Json.fromString(cand.fullName),
          "ctexs" -> Json.fromValues(data.ctexs.map(ctexJson))
        ))
      }),
      "unsafe" -> Json.fromValues(res.unsafe.toSeq.sortBy(_._1).map { case (cand, data) =>
        Json.fromFields(Seq(
          "function" -> Json.fromString(cand.fullName),
          "self" -> Json.fromValues(data.self.map(unsafeCtexJson)),
          "auxiliaries" -> Json.fromFields(
            data.auxiliaries.toSeq.map { case (aux, ctexs) =>
              aux.fullName -> Json.fromValues(ctexs.map(unsafeCtexJson))
            }.sortBy(_._1)
          )
        ))
      }),
      "unknownSafety" -> Json.fromValues(res.unknownsSafety.toSeq.sortBy(_._1).map { case (cand, data) =>
        Json.fromFields(Seq(
          "function" -> Json.fromString(cand.fullName),
          "self" -> Json.fromValues(data.self.map(unknownVCJson)),
          "auxiliaries" -> Json.fromFields(
            data.auxiliaries.toSeq.map { case (aux, ctexs) =>
              aux.fullName -> Json.fromValues(ctexs.map(unknownVCJson))
            }.sortBy(_._1)
          )
        ))
      }),
      "unknownEquivalence" -> Json.fromValues(unknownsEquiv.sorted.map(Json.fromString)),
      "wrong" -> Json.fromValues(wrongs.sorted.map(Json.fromString)),
      "weights" -> Json.fromFields(weights.map { case (mod, w) => mod -> Json.fromInt(w) })
    ))
    JsonUtils.writeFile(out, json)
  }

  private def explainAndSayFarewell(reason: EquivalenceChecker.FailureReason): Nothing = {
    def pretty(reason: EquivalenceChecker.TestExtractionFailure): String = reason match {
      case EquivalenceChecker.TestExtractionFailure.ModelTakesNoArg => "models do not take any argument"
      case EquivalenceChecker.TestExtractionFailure.ReturnTypeMismatch => "the return type is not a list"
      case EquivalenceChecker.TestExtractionFailure.UnknownExpr => "use of non-literal expression"
      case EquivalenceChecker.TestExtractionFailure.NoData => "no given samples"
      case EquivalenceChecker.TestExtractionFailure.UnificationFailure => "could not unify the sample type with models argument types"
    }
    val msg = reason match {
      case EquivalenceChecker.FailureReason.IllFormedTests(invalid) =>
        val msg = invalid.map { case (id, reason) => s"  ${id.fullName}: ${pretty(reason)}" }
        s"the following tests are ill-formed:\n${msg.mkString("\n")}"
      case EquivalenceChecker.FailureReason.NoModels => "there are no specified models"
      case EquivalenceChecker.FailureReason.NoFunctions => "there are no specified candidate functions"
      case EquivalenceChecker.FailureReason.ModelsSignatureMismatch(m1, m2) =>
        s"models ${m1.fullName} and ${m2.fullName} signatures do not match"
      case EquivalenceChecker.FailureReason.OverlappingModelsAndFunctions(overlapping) =>
        val verb = if (overlapping.size == 1) "is" else "are"
        s"${overlapping.mkString(", ")} $verb both candidate and model"
      case EquivalenceChecker.FailureReason.MultipleNormFunctions(norms) =>
        s"multiple norm functions are specified:\n${norms.toSeq.sorted.map(_.fullName).mkString("  ", "\n  ", "")}"
      case EquivalenceChecker.FailureReason.NormSignatureMismatch(norm) =>
        s"norm function ${norm.fullName} signature does not match with model signature"
      case EquivalenceChecker.FailureReason.IllegalHyperparameterValue(msg) => msg
    }
    context.reporter.fatalError(s"Could not create the equivalence check component because $msg")
  }

  override private[stainless] def execute(functions0: Seq[Identifier], symbols: trees.Symbols, exSummary: ExtractionSummary): Future[Analysis] =
    sys.error("Unreachable because def apply was overridden")

  extension (id: Identifier) {
    private def fullName: String = CheckFilter.fixedFullName(id)
  }
}
