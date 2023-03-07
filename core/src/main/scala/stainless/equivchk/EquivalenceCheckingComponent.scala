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
object optMaxPerm extends inox.IntOptionDef("equivchk-max-perm", EquivalenceChecker.defaultMaxMatchingPermutation, "<int>")
object optMaxCtex extends inox.IntOptionDef("equivchk-max-ctex", EquivalenceChecker.defaultMaxCtex, "<int>")

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
    extraction.utils.DebugPipeline("MeasureInference", MeasureInference(extraction.trees)) andThen
    extraction.utils.DebugPipeline("PartialEvaluation", PartialEvaluation(extraction.trees)) andThen
    extraction.completer(trees)

  override def apply(ids: Seq[Identifier], symbols: xt.Symbols): Future[Analysis] = {
    val (traceSyms, traceSummary) = tracePrePipeline.extract(symbols)
    val (plainSyms, plainSummary) = tracePostPipeline.extract(traceSyms)
    val ec = EquivalenceChecker.tryCreate(trace.trees)(traceSyms) match {
      case fail: EquivalenceChecker.Creation.Failure => explainAndSayFarewell(fail.reason)
      case success: EquivalenceChecker.Creation.Success => success.equivChker
    }
    val toProcess = createFilter.filter(ids, plainSyms, underlyingRun.component)
    for {
      gen <- underlyingRun.execute(toProcess, plainSyms, ExtractionSummary.Node(traceSummary, plainSummary))
      invalidVCsCands = counterExamples(gen).flatMap {
        case (vc, ctex) => ec.reportErroneous(gen.program)(gen, ctex)(vc.fid).getOrElse(Set.empty)
      }.toSeq.distinct
      _ = debugInvalidVCsCandidates(invalidVCsCands)
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
    val errns = trRes.erroneous.toSeq.sortBy(_._1).map {
      case (errn, data) =>
        val fd = ec.symbols.getFunction(errn)
        Record(errn, fd.getPos, data.solvingInfo.map(_.time).getOrElse(0L),
          Status.Equivalence(EquivalenceStatus.Erroneous),
          data.solvingInfo.flatMap(_.solverName), "equivalence", fd.source)
    }
    val wrgs = trRes.wrongs.toSeq.sorted.map { wrong =>
      val fd = ec.symbols.getFunction(wrong)
      // No solver or time specified because it's a signature mismatch
      Record(wrong, fd.getPos, 0L, Status.Equivalence(EquivalenceStatus.Wrong), None, "equivalence", fd.source)
    }
    val unknws = trRes.unknowns.toSeq.sortBy(_._1).map {
      case (unknown, data) =>
        val fd = ec.symbols.getFunction(unknown)
        Record(unknown, fd.getPos, data.solvingInfo.time, Status.Equivalence(EquivalenceStatus.Unknown), data.solvingInfo.solverName, "equivalence", fd.source)
    }

    val allRecords = genRecors ++ valid ++ errns ++ wrgs ++ unknws
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
      case (vc, VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), _, _)) =>
        vc -> model
    }.toMap
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

  private def debugPruned(ec: EquivalenceChecker)(pruned: Map[Identifier, ec.PruningReason]): Unit = {
    def pretty(fn: Identifier, reason: ec.PruningReason): String = {
      val rsonStr = reason match {
        case ec.PruningReason.SignatureMismatch => "signature mismatch"
        case ec.PruningReason.ByTest(testId, sampleIx, ctex) =>
          s"test falsification by ${testId.fullName} sample n°${sampleIx + 1} with ${prettyCtex(ec)(ctex.mapping)}\n    Expected: ${ctex.expected} but got: ${ctex.got}"
        case ec.PruningReason.ByPreviousCtex(ctex) => s"counter-example falsification with ${prettyCtex(ec)(ctex.mapping)}\n    Expected: ${ctex.expected} but got: ${ctex.got}"
      }
      s"${fn.fullName}: $rsonStr"
    }

    if (pruned.nonEmpty) {
      context.reporter.whenDebug(DebugSectionEquivChk) { debug =>
        debug("The following functions were pruned:")
        val strs = pruned.toSeq.sortBy(_._1).map(pretty.tupled)
        strs.foreach(s => debug(s"  $s"))
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
          val ctexStr = ctexs.map(prettyCtex(ec)(_)).map(s => s"  $s").mkString("\n  ")
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
    val errns = res.erroneous.keys.toSeq.map(_.fullName).sorted.mkString(", ")
    val unknowns = res.unknowns.keys.toSeq.map(_.fullName).sorted.mkString(", ")
    val wrongs = res.wrongs.toSeq.map(_.fullName).sorted.mkString(", ")
    info(s"List of erroneous functions: $errns")
    info(s"List of timed-out functions: $unknowns")
    info(s"List of wrong functions: $wrongs")
    info(s"Printing the final state:")
    res.valid.foreach { case (cand, data) =>
      val pathStr = data.path.map(_.fullName).mkString(", ")
      info(s"Path for the function ${cand.fullName}: $pathStr")
    }
    res.erroneous.foreach { case (cand, data) =>
      val ctexsStr = data.ctexs.map(ctex => ctex.map { case (vd, arg) => s"${vd.id.name} -> $arg" }.mkString(", "))
      info(s"Counterexample for the function ${cand.fullName}:")
      ctexsStr.foreach(s => info(s"  $s"))
    }
  }

  private def prettyCtex(ec: EquivalenceChecker)(ctex: Map[ec.trees.ValDef, ec.trees.Expr]): String =
    ctex.toSeq.map { case (vd, e) => s"${vd.id.name} -> $e" }.mkString(", ")

  private def dumpResultsJson(out: File, ec: EquivalenceChecker)(res: ec.Results): Unit = {
    val equivs = res.equiv.map { case (m, l) => m.fullName -> l.map(_.fullName).toSeq.sorted }
      .toSeq.sortBy(_._1)
    val errns = res.erroneous.keys.toSeq.map(_.fullName).sorted
    val unknowns = res.unknowns.keys.toSeq.map(_.fullName).sorted
    val wrongs = res.wrongs.toSeq.map(_.fullName).sorted

    val json = Json.fromFields(Seq(
      "equivalent" -> Json.fromValues(equivs.map { case (m, l) =>
        Json.fromFields(Seq(
          "model" -> Json.fromString(m),
          "functions" -> Json.fromValues(l.map(Json.fromString))
        ))
      }),
      "erroneous" -> Json.fromValues(errns.map(Json.fromString)),
      "timeout" -> Json.fromValues(unknowns.sorted.map(Json.fromString)),
      "wrong" -> Json.fromValues(wrongs.sorted.map(Json.fromString)),
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
