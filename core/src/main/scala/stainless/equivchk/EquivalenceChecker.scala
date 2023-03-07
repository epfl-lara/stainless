/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package equivchk

import inox.utils.Position
import io.circe.{Json, JsonObject}
import stainless.equivchk.EquivalenceChecker._
import stainless.extraction.trace._
import stainless.utils.{CheckFilter, JsonUtils}
import stainless.verification.{VCResult, VCStatus, VerificationAnalysis}
import stainless.{FreshIdentifier, Identifier, Program, StainlessProgram, evaluators}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.math.Ordering.IntOrdering
import scala.util.control.NonFatal

// EquivalenceChecker workflow consists of a preliminary analysis and examinations made up of rounds.
//
// The preliminary analysis is done outside of EquivalenceChecker: it is a general verification pass over all candidates
// to catch for invalid VCs (such as division by zero and so on).
// These invalid VCs are communicated to EquivalenceChecker with reportErroneous.
// Candidates having at least one invalid VCs are classified as "erroneous" and
// are not considered for equivalence checking any further.
//
// After this pass, EquivalenceChecker works in examination and rounds.
// First, we pick a candidate to examine with `pickNextExamination` returning a `NextExamination`
// The picked candidate will be checked for equivalence against models according to various strategies.
// For each strategy, we prepare a so-called "round" with `prepareRound` which will return functions encoding
// equivalence checking condition according to that strategy.
// These functions are then sent to the solver, and the results are communicated back to EquivalenceChecker with `concludeRound`.
// Depending on the result, we can either classify the candidate and go with the next examination
// (indicated by `concludeRound` returning RoundConclusion.CandidateClassified) or we need to try a new strategy
// and go with the next round (`concludeRound` returning RoundConclusion.NextRound).
//
// The strategies are applied in the following order:
// -Pick the top 3 models according to their score.
// -Repeat until we are done or we have tried all 3 models:
//    -"Model first without sublemmas": we try to prove equivalence by using the selected model as template for induction.
//    Functions inside the candidate and the model do not get any special treatment.
//    If the equiv. check succeeds, the candidate is correct.
//    Otherwise, if it is invalid, the candidate is classified as erroneous (i.e., not equivalent, it is incorrect)
//    If it is inconclusive (timeout), we try the next strategy.
//    -"Candidate first without sublemmas": as above, except we use the candidate as template for induction
//    -"Model first with sublemmas": uses the selected model for induction; functions calls appearing in model and candidate
//    are matched against each other and are checked for equivalence as well.
//    If these subfunctions equivalence all succeed, we are done.
//    Otherwise (invalid results or timeout), we try another matching of function until we have tried all of them.
//    Note that an invalid result does not necessarily mean that the candidate is incorrect, it may be the case that
//    the matching of function calls we have tried is not the good one.
//    -"Candidate first with sublemmas": as above but we use the candidate for the induction
//    -If all these strategies are inconclusive, try with the next model (until we have tried all of the 3).
//
class EquivalenceChecker(override val trees: Trees,
                         private val allModels: Seq[Identifier],
                         private val allCandidates: Seq[Identifier],
                         private val norm: Option[Identifier],
                         private val N: Int,
                         private val initScore: Int,
                         private val maxMatchingPermutation: Int,
                         private val maxCtex: Int,
                         private val maxStepsEval: Int)
                        (private val tests: Map[Identifier, (Seq[trees.Expr], Seq[trees.Type])],
                         val symbols: trees.Symbols)
                        (using val context: inox.Context)
  extends Utils with stainless.utils.CtexRemapping { self =>
  import trees._

  //region Examination and rounds ADTs

  enum NextExamination {
    // In both `Done` and `NewCandidate`, `pruned` contains candidates functions that got classified
    // without needing any further examination.
    case Done(pruned: Map[Identifier, PruningReason], results: Results)
    case NewCandidate(cand: Identifier, model: Identifier, strat: EquivCheckStrategy, pruned: Map[Identifier, PruningReason])
  }

  enum RoundConclusion {
    case NextRound(cand: Identifier,
                   model: Identifier,
                   strat: EquivCheckStrategy,
                   prunedSubFnsPairs: Set[(Identifier, Identifier, ArgPermutation)])
    case CandidateClassified(cand: Identifier,
                             classification: Classification,
                             prunedSubFnsPairs: Set[(Identifier, Identifier, ArgPermutation)])
  }

  enum Classification {
    case Valid(directModel: Identifier)
    case Invalid(ctex: Seq[Map[ValDef, Expr]])
    case Unknown
  }

  enum PruningReason {
    case SignatureMismatch
    case ByTest(testId: Identifier, sampleIx: Int, ctex: Ctex)
    case ByPreviousCtex(ctex: Ctex)
  }
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Final results definitions

  case class Results(// Clusters
                     equiv: Map[Identifier, Set[Identifier]],
                     valid: Map[Identifier, ValidData],
                     // Incorrect, either due to not being equivalent or having invalid VCs
                     erroneous: Map[Identifier, ErroneousData],
                     // Candidates that will need to be manually inspected...
                     unknowns: Map[Identifier, UnknownData],
                     // Incorrect signature
                     wrongs: Set[Identifier])
  case class Ctex(mapping: Map[ValDef, Expr], expected: Expr, got: Expr)
  case class ValidData(path: Seq[Identifier], solvingInfo: SolvingInfo)
  // The list of counter-examples can be empty; the candidate is still invalid but a ctex could not be extracted
  // If the solvingInfo is None, the candidate has been pruned.
  case class ErroneousData(ctexs: Seq[Map[ValDef, Expr]], solvingInfo: Option[SolvingInfo])
  case class UnknownData(solvingInfo: SolvingInfo)
  // Note: fromCache and trivial are only relevant for valid candidates
  case class SolvingInfo(time: Long, solverName: Option[String], fromCache: Boolean, trivial: Boolean) {
    def withAddedTime(extra: Long): SolvingInfo = copy(time = time + extra)
  }

  def getCurrentResults(): Results = {
    val equiv = clusters.map { case (model, clst) => model -> clst.toSet }.toMap
    Results(equiv, valid.toMap, erroneous.toMap, unknowns.toMap, signatureMismatch.toSet)
  }
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Definitions for strategies

  enum EquivCheckOrder {
    case ModelFirst
    case CandidateFirst
  }

  case class EquivCheckStrategy(order: EquivCheckOrder, subFnsMatchingStrat: Option[SubFnsMatchingStrat]) {
    def pretty: String = (order, subFnsMatchingStrat) match {
      case (EquivCheckOrder.ModelFirst, None) => "model first without sublemmas"
      case (EquivCheckOrder.CandidateFirst, None) => "candidate first without sublemmas"
      case (EquivCheckOrder.ModelFirst, Some(matchingStrat)) => s"model first with sublemmas: ${matchingStrat.curr.pretty}"
      case (EquivCheckOrder.CandidateFirst, Some(matchingStrat)) => s"candidate first with sublemmas: ${matchingStrat.curr.pretty}"
    }
  }

  object EquivCheckStrategy {
    def init: EquivCheckStrategy = EquivCheckStrategy(EquivCheckOrder.ModelFirst, None)
  }

  // Pairs of model - candidate sub functions with argument permutation
  type SubFnsMatching = Matching[Identifier, ArgPermutation]

  case class SubFnsMatchingStrat(curr: SubFnsMatching, rest: Seq[SubFnsMatching], all: Seq[SubFnsMatching])

  extension (matching: SubFnsMatching) {
    def pretty: String = matching.pairs
      .map { case ((mod, cand), perm) =>
        s"${CheckFilter.fixedFullName(mod)} <-> ${CheckFilter.fixedFullName(cand)} (permutation = ${perm.m2c.mkString(", ")})"
      }
      .mkString(", ")
  }
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Private state

  private val ctexEvalPermutationLimit = 16

  private enum ExaminationState {
    case PickNext
    case Examining(candidate: Identifier, roundState: RoundState)
  }

  private case class RoundState(model: Identifier,
                                remainingModels: Seq[Identifier],
                                strat: EquivCheckStrategy,
                                equivLemmas: EquivLemmas,
                                cumulativeSolvingTime: Long)

  private enum EquivLemmas {
    case ToGenerate
    case Generated(eqLemma: Identifier,
                   proof: Option[Identifier],
                   sublemmas: Seq[Identifier])
  }

  private case class EquivCheckConf(model: FunDef, candidate: FunDef, strat: EquivCheckStrategy, topLevel: Boolean) {
    val (fd1, fd2) = strat.order match {
      case EquivCheckOrder.ModelFirst => (model, candidate)
      case EquivCheckOrder.CandidateFirst => (candidate, model)
    }
  }

  // Function called from a candidate (callee) -> candidate(s) (caller)
  // (may include themselves)
  private val candidatesCallee: Map[Identifier, Set[Identifier]] = {
    allCandidates.foldLeft(Map.empty[Identifier, Set[Identifier]]) {
      case (acc, cand) =>
        val callees = symbols.transitiveCallees(cand)
        callees.foldLeft(acc) {
          case (acc, callee) =>
            val curr = acc.getOrElse(callee, Set.empty)
            acc + (callee -> (curr + cand))
        }
    }
  }

  private val models = mutable.LinkedHashMap.from(allModels.map(_ -> initScore))
  private val remainingCandidates = mutable.LinkedHashSet.from(allCandidates)
  // Candidate -> set of models for tested so far for the candidate, but resulted in an unknown
  private val candidateTestedModels = mutable.Map.from(allCandidates.map(_ -> mutable.Set.empty[Identifier]))
  private var nbExaminedCandidates = allCandidates.size
  private var examinationState: ExaminationState = ExaminationState.PickNext
  private val valid = mutable.Map.empty[Identifier, ValidData]
  // candidate -> list of counter-examples (can be empty, in which case the candidate is invalid but a ctex could not be extracted)
  private val erroneous = mutable.Map.empty[Identifier, ErroneousData]
  private val unknowns = mutable.LinkedHashMap.empty[Identifier, UnknownData]
  private val signatureMismatch = mutable.ArrayBuffer.empty[Identifier]
  private val clusters = mutable.Map.empty[Identifier, mutable.ArrayBuffer[Identifier]]

  // Type -> multiplicity
  private case class UnordSig(args: Map[Type, Int])
  // Type -> list of values, whose length is the multiplicity of the type
  private case class UnordCtex(args: Map[Type, Seq[Expr]])
  private val ctexsDb = mutable.Map.empty[UnordSig, mutable.Set[UnordCtex]]

  // Set of model subfn - candidate subfn for which we know (by counter example falsification) that do not match
  // This is useful for pruning invalid matching without having to re-evaluate the pair.
  private val invalidFunctionsPairsCache = mutable.Set.empty[(Identifier, Identifier, ArgPermutation)]
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Public API

  def reportErroneous(pr: StainlessProgram)(analysis: VerificationAnalysis, counterex: pr.Model)(fun: Identifier): Option[Set[Identifier]] = {
    if (allCandidates.contains(fun)) {
      remainingCandidates -= fun
      val ordCtexs = ctexOrderedArguments(fun, pr)(counterex.vars).toSeq
      ordCtexs.foreach(addCtex)
      val fd = symbols.functions(fun)
      val ctexVars = ordCtexs.map(ctex => fd.params.zip(ctex).toMap)
      erroneous += fun -> ErroneousData(ctexVars, Some(extractSolvingInfo(analysis, fun, Seq.empty)))
      Some(Set(fun))
    } else candidatesCallee.get(fun) match {
      case Some(cands) =>
        // This means this erroneous `fun` is called by all candidates in `cands`.
        // `cands` should be of size 1 because a function called by multiple candidates must be either a library fn or
        // a provided function which are all assumed to be correct.
        cands.foreach { cand =>
          remainingCandidates -= cand
          // No ctex available, because counterex corresponds to the signature of `fun` not necessarily `cand`
          erroneous += cand -> ErroneousData(Seq.empty, Some(extractSolvingInfo(analysis, cand, Seq.empty)))
        }
        Some(cands)
      case None =>
        // Nobody knows about this function
        None
    }
  }

  def pickNextExamination(): NextExamination = {
    assert(examinationState == ExaminationState.PickNext)

    val anyModel = symbols.functions(allModels.head)
    var picked: Option[Identifier] = None
    val pruned = mutable.Map.empty[Identifier, PruningReason]
    while (picked.isEmpty && remainingCandidates.nonEmpty) {
      val candId = remainingCandidates.head
      remainingCandidates -= candId
      val cand = symbols.functions(candId)

      if (areSignaturesCompatible(cand, anyModel)) {
        evalCheck(anyModel, cand) match {
          case EvalCheck.Ok =>
            picked = Some(candId)
          case EvalCheck.FailsTest(testId, sampleIx, ctex) =>
            erroneous += candId -> ErroneousData(Seq(ctex.mapping), None)
            pruned += candId -> PruningReason.ByTest(testId, sampleIx, ctex)
          case EvalCheck.FailsCtex(ctex) =>
            erroneous += candId -> ErroneousData(Seq(ctex.mapping), None)
            pruned += candId -> PruningReason.ByPreviousCtex(ctex)
        }
      } else {
        signatureMismatch += candId
        pruned += candId -> PruningReason.SignatureMismatch
      }
    }

    picked match {
      case Some(candId) =>
        val topN = models.toSeq
            .filter { case (mod, _ ) => !candidateTestedModels(candId).contains(mod) } // Do not test models for which this candidate got an unknown
            .sortBy(-_._2)
            .take(N).map(_._1)
        if (topN.nonEmpty) {
          val strat = EquivCheckStrategy.init
          examinationState = ExaminationState.Examining(candId, RoundState(topN.head, topN.tail, strat, EquivLemmas.ToGenerate, 0L))
          NextExamination.NewCandidate(candId, topN.head, strat, pruned.toMap)
        } else {
          pickNextExamination() match {
            case d@NextExamination.Done(_, _) => d.copy(pruned = pruned.toMap ++ d.pruned)
            case nc@NextExamination.NewCandidate(_, _, _, _) => nc.copy(pruned = pruned.toMap ++ nc.pruned)
          }
        }
      case None =>
        if (unknowns.nonEmpty && unknowns.size < nbExaminedCandidates) {
          nbExaminedCandidates = unknowns.size
          remainingCandidates ++= unknowns.keys
          unknowns.clear()
          pickNextExamination() match {
            case d@NextExamination.Done(_, _) => d.copy(pruned = pruned.toMap ++ d.pruned)
            case nc@NextExamination.NewCandidate(_, _, _, _) => nc.copy(pruned = pruned.toMap ++ nc.pruned)
          }
        } else {
          NextExamination.Done(pruned.toMap, getCurrentResults())
        }
    }
  }

  def prepareRound(): Seq[FunDef] = {
    val (cand, roundState) = examinationState match {
      case ExaminationState.Examining(cand, roundState) => (cand, roundState)
      case ExaminationState.PickNext =>
        sys.error("Trace must be in `Examining` state")
    }
    assert(roundState.equivLemmas == EquivLemmas.ToGenerate)
    val conf = EquivCheckConf(symbols.functions(roundState.model), symbols.functions(cand), roundState.strat, topLevel = true)
    val generated = equivalenceCheck(conf)
    val equivLemmas = EquivLemmas.Generated(generated.eqLemma.id, generated.proof.map(_.id), generated.sublemmasAndReplFns.map(_.id))
    examinationState = ExaminationState.Examining(cand, roundState.copy(equivLemmas = equivLemmas))
    generated.eqLemma +: (generated.proof.toSeq ++ generated.sublemmasAndReplFns)
  }

  def concludeRound(analysis: VerificationAnalysis): RoundConclusion = examinationState match {
    case ExaminationState.Examining(cand, RoundState(model, remainingModels, strat, EquivLemmas.Generated(eqLemma, proof, sublemmas), currCumulativeSolvingTime)) =>
      val solvingInfo = extractSolvingInfo(analysis, cand, eqLemma +: (proof.toSeq ++ sublemmas))

      def nextRoundOrUnknown(): RoundConclusion = {
        models(model) = models(model) - 1
        (strat.order, strat.subFnsMatchingStrat) match {
          case (EquivCheckOrder.ModelFirst, None) =>
            val nextStrat = EquivCheckStrategy(EquivCheckOrder.CandidateFirst, None)
            val nextRS = RoundState(model, remainingModels, nextStrat, EquivLemmas.ToGenerate, currCumulativeSolvingTime + solvingInfo.time)
            examinationState = ExaminationState.Examining(cand, nextRS)
            RoundConclusion.NextRound(cand, model, nextStrat, Set.empty)

          case (EquivCheckOrder.CandidateFirst, None) =>
            val subFnsMatching = allSubFnsMatches(model, cand)
            val pruned = pruneSubFnsMatching(subFnsMatching)
            if (pruned.passed.isEmpty) {
              // No matching for subfunctions available, we pick the next model if available
              nextModelOrUnknown(pruned.invalidPairs)
            } else {
              val nextStrat = EquivCheckStrategy(EquivCheckOrder.ModelFirst,
                Some(SubFnsMatchingStrat(pruned.passed.head, pruned.passed.tail, pruned.passed)))
              val nextRS = RoundState(model, remainingModels, nextStrat, EquivLemmas.ToGenerate, currCumulativeSolvingTime + solvingInfo.time)
              examinationState = ExaminationState.Examining(cand, nextRS)
              RoundConclusion.NextRound(cand, model, nextStrat, pruned.invalidPairs)
            }

          case (EquivCheckOrder.ModelFirst, Some(matchingStrat)) =>
            // Prune the remaining once again, maybe we got new ctex in the meantime
            val pruned = pruneSubFnsMatching(matchingStrat.rest)
            if (pruned.passed.nonEmpty) {
              // Try with the next matching
              val nextStrat = EquivCheckStrategy(EquivCheckOrder.ModelFirst,
                Some(matchingStrat.copy(curr = pruned.passed.head, rest = pruned.passed.tail)))
              val nextRS = RoundState(model, remainingModels, nextStrat, EquivLemmas.ToGenerate, currCumulativeSolvingTime + solvingInfo.time)
              examinationState = ExaminationState.Examining(cand, nextRS)
              RoundConclusion.NextRound(cand, model, nextStrat, pruned.invalidPairs)
            } else {
              // Move to function first with subfns matching, if possible
              // Reuse the computed matching instead of computing it again,
              // but prune it once again, maybe we got new ctex in the meantime.
              val allPruned = pruneSubFnsMatching(matchingStrat.all)
              if (allPruned.passed.isEmpty) {
                // No matching for subfunctions available.
                // We pick the next model if available
                nextModelOrUnknown(pruned.invalidPairs ++ allPruned.invalidPairs)
              } else {
                val nextStrat = EquivCheckStrategy(EquivCheckOrder.CandidateFirst,
                  Some(SubFnsMatchingStrat(
                    allPruned.passed.head, allPruned.passed.tail,
                    // Update `all` with its re-pruned version
                    allPruned.passed)))
                val nextRS = RoundState(model, remainingModels, nextStrat, EquivLemmas.ToGenerate, currCumulativeSolvingTime + solvingInfo.time)
                examinationState = ExaminationState.Examining(cand, nextRS)
                RoundConclusion.NextRound(cand, model, nextStrat, pruned.invalidPairs ++ allPruned.invalidPairs)
              }
            }

          case (EquivCheckOrder.CandidateFirst, Some(matchingStrat)) =>
            val pruned = pruneSubFnsMatching(matchingStrat.rest)
            if (pruned.passed.nonEmpty) {
              // Try with the next matching
              val nextStrat = EquivCheckStrategy(EquivCheckOrder.CandidateFirst,
                Some(matchingStrat.copy(curr = pruned.passed.head, rest = pruned.passed.tail)))
              val nextRS = RoundState(model, remainingModels, nextStrat, EquivLemmas.ToGenerate, currCumulativeSolvingTime + solvingInfo.time)
              examinationState = ExaminationState.Examining(cand, nextRS)
              RoundConclusion.NextRound(cand, model, nextStrat, pruned.invalidPairs)
            } else {
              nextModelOrUnknown(pruned.invalidPairs)
            }
        }
      }
      def nextModelOrUnknown(invalidPairs: Set[(Identifier, Identifier, ArgPermutation)]): RoundConclusion = {
        candidateTestedModels(cand) += model
        if (remainingModels.nonEmpty) {
          val nextStrat = EquivCheckStrategy.init
          val nextRS = RoundState(remainingModels.head, remainingModels.tail, nextStrat, EquivLemmas.ToGenerate, currCumulativeSolvingTime + solvingInfo.time)
          examinationState = ExaminationState.Examining(cand, nextRS)
          RoundConclusion.NextRound(cand, remainingModels.head, nextStrat, invalidPairs)
        } else {
          // oh no, manual inspection incoming
          examinationState = ExaminationState.PickNext
          unknowns += cand -> UnknownData(solvingInfo.withAddedTime(currCumulativeSolvingTime))
          RoundConclusion.CandidateClassified(cand, Classification.Unknown, invalidPairs)
        }
      }

      /////////////////////////////////////////////////////////////////////////////////////

      val report = analysis.toReport
      val allCtexs = analysis.vrs.collect {
        case (vc, VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), _, _)) =>
          ctexOrderedArguments(vc.fid, model.program)(model.vars).map(vc.fid -> _)
      }.flatten.groupMap(_._1)(_._2)

      if (report.totalInvalid != 0) {
        assert(allCtexs.nonEmpty, "Conspiration!")
        allCtexs.foreach { case (_, ctexs) =>
          ctexs.foreach(addCtex)
        }
        if (strat.subFnsMatchingStrat.isDefined) {
          nextRoundOrUnknown()
        } else {
          // schade
          val candFd = symbols.functions(cand)
          // Take all ctex for `cand`, `eqLemma` and `proof`
          val ctexOrderedArgs = (Seq(cand, eqLemma) ++ proof.toSeq).flatMap(id => allCtexs.getOrElse(id, Seq.empty))
          val ctexsMap = ctexOrderedArgs.map(ctex => candFd.params.zip(ctex).toMap)
          erroneous += cand -> ErroneousData(ctexsMap, Some(solvingInfo.withAddedTime(currCumulativeSolvingTime)))
          examinationState = ExaminationState.PickNext
          RoundConclusion.CandidateClassified(cand, Classification.Invalid(ctexsMap), Set.empty)
        }
      } else if (report.totalUnknown != 0) {
        nextRoundOrUnknown()
      } else {
        assert(!models.contains(cand))
        val modelPath = valid.get(model).map(_.path).getOrElse(Seq.empty)
        valid += cand -> ValidData(model +: modelPath, solvingInfo.withAddedTime(currCumulativeSolvingTime))
        val currScore = models(model)
        models(model) = currScore + (if (currScore > 0) 20 else 100)
        models(cand) = 0 // Welcome to the privileged club of models!
        clusters.getOrElseUpdate(model, mutable.ArrayBuffer.empty) += cand
        examinationState = ExaminationState.PickNext
        RoundConclusion.CandidateClassified(cand, Classification.Valid(model), Set.empty)
      }

    case _ => sys.error("Trace must be in `Examining` state with `Generated` lemmas")
  }
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Generation of functions encoding equivalence

  private case class GeneratedEqLemmas(eqLemma: FunDef, proof: Option[FunDef], sublemmasAndReplFns: Seq[FunDef])

  // Generate eqLemma and sublemmas for the given top-level model and candidate functions
  private def equivalenceCheck(conf: EquivCheckConf): GeneratedEqLemmas = {
    import conf.{fd1, fd2}
    import exprOps._

    // For the top-level model and candidate function
    val permutation = ArgPermutation(conf.model.params.indices) // No permutation for top-level model and candidate
    val (eqLemmaResTopLvl, topLvlRepl) = generateEqLemma(conf, permutation)
    // For the sub-functions
    val eqLemmasResSubs = conf.strat.subFnsMatchingStrat.toSeq.flatMap { matchingStrat =>
      matchingStrat.curr.pairs.flatMap {
        case ((submod, subcand), perm) =>
          val newConf = conf.copy(model = symbols.functions(submod), candidate = symbols.functions(subcand), topLevel = false)
          val (subres, subRepl) = generateEqLemma(newConf, perm)
          Seq(subres.updatedFd) ++ subres.helper.toSeq ++ subRepl.toSeq
      }
    }

    GeneratedEqLemmas(eqLemmaResTopLvl.updatedFd, eqLemmaResTopLvl.helper, topLvlRepl.toSeq ++ eqLemmasResSubs)
  }

  // Generate an eqLemma for the given fd1 and fd2 functions and the given permutation for the candidate function
  private def generateEqLemma(conf: EquivCheckConf, perm: ArgPermutation): (ElimTraceInduct, Option[FunDef]) = {
    import conf.{fd1, fd2}
    import exprOps._

    assert(areSignaturesCompatibleModuloPerm(conf.model, conf.candidate, perm)) // i.e. fd1 and fd2
    val freshId = FreshIdentifier(CheckFilter.fixedFullName(fd1.id) + "$" + CheckFilter.fixedFullName(fd2.id))
    val eqLemma0 = exprOps.freshenSignature(fd1).copy(id = freshId)

    // Body of fd2, with calls to subfunctions replaced
    val fd2Repl = conf.strat.subFnsMatchingStrat.map { matchingStrat =>
      val replMap = matchingStrat.curr.pairs.map {
        case ((submod, subcand), perm) =>
          conf.strat.order match {
            case EquivCheckOrder.ModelFirst =>
              // f1 = model and f2 = candidate, and we want to replace all calls to candidate subfunctions by their models counterpart
              subcand -> (submod, perm.m2c)
            case EquivCheckOrder.CandidateFirst =>
              // Note: perm gives the permutation model ix -> cand ix, so we need to reverse it here
              submod -> (subcand, perm.reverse.m2c)
          }
      }
      inductPattern(symbols, fd2, fd2, "replacement", replMap)
        .setPos(fd2.getPos)
        .copy(flags = Seq(Derived(Some(fd2.id))))
    }

    val newParamTps = eqLemma0.tparams.map { tparam => tparam.tp }
    val newParamVars = eqLemma0.params.map { param => param.toVariable }

    val subst = {
      val nweParamVarsPermuted = conf.strat.order match {
        case EquivCheckOrder.ModelFirst =>
          // f1 = model, f2 = candidate, so no re-ordering
          newParamVars
        case EquivCheckOrder.CandidateFirst =>
          // f1 = candidate, f2 = model: we need to "undo" the ordering
          perm.m2c.map(newParamVars)
      }
      (conf.model.params.map(_.id) zip nweParamVarsPermuted).toMap
    }
    val tsubst = (conf.model.tparams zip newParamTps).map { case (tparam, targ) => tparam.tp.id -> targ }.toMap
    val specializer = new Specializer(eqLemma0, eqLemma0.id, tsubst, subst, Map())

    val specs = BodyWithSpecs(conf.model.fullBody).specs.filter(s => s.kind == LetKind || s.kind == PreconditionKind)
    val pre = specs.map {
      case Precondition(cond) => Precondition(specializer.transform(cond))
      case LetInSpec(vd, expr) => LetInSpec(vd, specializer.transform(expr))
    }
    val (paramsFun1, paramsFun2) = {
      conf.strat.order match {
        case EquivCheckOrder.ModelFirst =>
          // f1 = model, f2 = candidate
          (newParamVars, perm.reverse.m2c.map(newParamVars))
        case EquivCheckOrder.CandidateFirst =>
          (newParamVars, perm.m2c.map(newParamVars))
      }
    }
    val fun1 = FunctionInvocation(fd1.id, newParamTps, paramsFun1)
    val fun2 = FunctionInvocation(fd2Repl.map(_.id).getOrElse(fd2.id), newParamTps, paramsFun2)

    val (normFun1, normFun2) = norm match {
      case Some(n) if conf.topLevel => // Norm applies only to top-level model & candidate functions
        (FunctionInvocation(n, newParamTps, newParamVars :+ fun1),
          FunctionInvocation(n, newParamTps, newParamVars :+ fun2))
      case _ => (fun1, fun2)
    }

    val res = ValDef.fresh("res", UnitType())
    val cond = Equals(normFun1, normFun2)
    val post = Postcondition(Lambda(Seq(res), cond))
    val body = UnitLiteral()
    val withPre = exprOps.reconstructSpecs(pre, Some(body), UnitType())
    val eqLemma1 = eqLemma0.copy(
      fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed,
      flags = Seq(Derived(Some(fd1.id)), Annotation("traceInduct", List(StringLiteral(fd1.id.name)))),
      returnType = UnitType()
    )
    val elim = elimTraceInduct(symbols, eqLemma1)
      .getOrElse(sys.error("Impossible, eqLemma is annotated with @traceInduct"))
    (elim, fd2Repl)
  }
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Evaluation of model & function with collected counter-examples

  private enum EvalCheck {
    case Ok
    case FailsTest(testId: Identifier, sampleIx: Int, ctex: Ctex)
    case FailsCtex(ctex: Ctex)
  }

  // Eval check for top level candidate and model
  private def evalCheck(model: FunDef, cand: FunDef): EvalCheck = {
    assert(areSignaturesCompatible(model, cand))

    def passAllTests: Option[EvalCheck.FailsTest] = {
      def passTest(id: Identifier): Option[EvalCheck.FailsTest] = {
        val (samples, instParams) = tests(id)
        findMap(samples.zipWithIndex) { case (arg, sampleIx) =>
          passTestSample(arg, instParams).map(_ -> sampleIx)
        }.map { case ((evalArgs, expected, got), sampleIx) =>
          EvalCheck.FailsTest(id, sampleIx, Ctex(cand.params.zip(evalArgs).toMap, expected, got))
        }
      }

      def loop(tests: Seq[Identifier]): Option[EvalCheck.FailsTest] = {
        if (tests.isEmpty) None
        else passTest(tests.head) match {
          case Some(f) => Some(f)
          case None => loop(tests.tail)
        }
      }

      loop(tests.keys.toSeq)
    }

    def passTestSample(arg: Expr, instTparams: Seq[Type]): Option[(Seq[Expr], Expr, Expr)] = {
      val evalArg = try {
        evaluate(arg) match {
          case inox.evaluators.EvaluationResults.Successful(evalArg) => evalArg
          case _ =>
            return None // If we cannot evaluate the argument (which should be a tuple), then we consider this test to be "successful"
        }
      } catch {
        case NonFatal(_) => return None
      }
      val argsSplit = evalArg match {
        case Tuple(args) => args
        case _ => return None // ditto, we will not crash
      }

      val invocationCand = FunctionInvocation(cand.id, instTparams, argsSplit)
      val invocationModel = FunctionInvocation(allModels.head, instTparams, argsSplit) // any model will do
      try {
        (evaluate(invocationCand), evaluate(invocationModel)) match {
          case (inox.evaluators.EvaluationResults.Successful(output), inox.evaluators.EvaluationResults.Successful(expected)) =>
            if (output == expected) None
            else Some((argsSplit, expected, output))
          case _ => None
        }
      } catch {
        case NonFatal(_) => None
      }
    }

    def evaluate(expr: Expr) = {
      val syms: symbols.type = symbols
      type ProgramType = inox.Program {val trees: self.trees.type; val symbols: syms.type}
      val prog: ProgramType = inox.Program(self.trees)(syms)
      val sem = new inox.Semantics {
        val trees: self.trees.type = self.trees
        val symbols: syms.type = syms
        val program: prog.type = prog

        def createEvaluator(ctx: inox.Context) = ???

        def createSolver(ctx: inox.Context) = ???
      }
      class EvalImpl(override val program: prog.type, override val context: inox.Context)
                    (using override val semantics: sem.type)
        extends evaluators.RecursiveEvaluator(program, context)
          with inox.evaluators.HasDefaultGlobalContext
          with inox.evaluators.HasDefaultRecContext

      val evaluator = new EvalImpl(prog, self.context)(using sem)
      evaluator.eval(expr)
    }

    val permutation = ArgPermutation(model.params.indices) // No permutation for top-level model and candidate
    passAllTests
      .orElse(evalCheckCtexOnly(model, cand, permutation).map(EvalCheck.FailsCtex.apply))
      .getOrElse(EvalCheck.Ok)
  }

  // Eval check for top level candidate and model and their subfunctions
  private def evalCheckCtexOnly(model: FunDef, cand: FunDef, candPerm: ArgPermutation): Option[Ctex] = {
    assert(areSignaturesCompatibleModuloPerm(model, cand, candPerm))
    val subst = TyParamSubst(IntegerType(), i => Some(IntegerLiteral(i)))

    def passUnordCtex(ctex: UnordCtex): Option[(Seq[Expr], Expr, Expr)] = {
      // From `ctex`, generate all possible ordered permutations of args according to the types
      // If the type multiplicity is 1 for all params, then there is only one ordered ctex possible
      val ctexSeq = ctex.args.toSeq
      val perms = cartesianProduct(ctexSeq.map { case (_, args) => args.permutations.toSeq })
      findMap(perms.take(ctexEvalPermutationLimit).toSeq) { perm =>
        assert(perm.size == ctexSeq.size, "Cartesian product is hard to grasp, yes")
        val permTpeMap: Map[Type, Seq[Expr]] = ctexSeq.map(_._1).zip(perm).toMap
        assert(permTpeMap.forall { case (tpe, args) => args.forall(_.getType(using symbols) == tpe) })

        // For each type, the current index within permTpeMap
        val tpeIxs = mutable.Map.from(ctexSeq.map(_._1 -> 0))
        val ordArgs = for (vd <- model.params) yield {
          val vdTpeInst = substTypeParams(model.tparams, vd.tpe)(using subst)
          val arg = permTpeMap(vdTpeInst)(tpeIxs(vdTpeInst))
          tpeIxs(vdTpeInst) = tpeIxs(vdTpeInst) + 1
          arg
        }
        passOrdCtex(ordArgs).map { case (exp, got) => (ordArgs, exp, got) }
      }
    }

    def passOrdCtex(args: Seq[Expr]): Option[(Expr, Expr)] = {
      val syms: symbols.type = symbols
      type ProgramType = inox.Program {val trees: self.trees.type; val symbols: syms.type}
      val prog: ProgramType = inox.Program(self.trees)(syms)
      val sem = new inox.Semantics {
        val trees: prog.trees.type = prog.trees
        val symbols: syms.type = prog.symbols
        val program: prog.type = prog

        def createEvaluator(ctx: inox.Context) = ???

        def createSolver(ctx: inox.Context) = ???
      }
      class EvalImpl(override val program: prog.type, override val context: inox.Context)
                    (using override val semantics: sem.type)
        extends evaluators.RecursiveEvaluator(program, context)
          with inox.evaluators.HasDefaultGlobalContext
          with inox.evaluators.HasDefaultRecContext {
        override lazy val maxSteps: Int = maxStepsEval
      }
      val evaluator = new EvalImpl(prog, self.context)(using sem)

      val tparams = model.tparams.map(_ => IntegerType())
      val invocationModel = evaluator.program.trees.FunctionInvocation(model.id, tparams, args)
      val invocationCand = evaluator.program.trees.FunctionInvocation(cand.id, tparams, candPerm.reverse.m2c.map(args))
      try {
        (evaluator.eval(invocationCand), evaluator.eval(invocationModel)) match {
          case (inox.evaluators.EvaluationResults.Successful(output), inox.evaluators.EvaluationResults.Successful(expected)) =>
            if (output == expected) None
            else Some((expected, output))
          case _ => None
        }
      } catch {
        case NonFatal(_) => None
      }
    }

    // Substitute tparams with IntegerType()
    val argsTpe = model.params.map(vd => substTypeParams(model.tparams, vd.tpe)(using subst))
    val unordSig = UnordSig(argsTpe.groupMapReduce(identity)(_ => 1)(_ + _))
    val ctexs = ctexsDb.getOrElse(unordSig, mutable.ArrayBuffer.empty)
    findMap(ctexs.toSeq)(passUnordCtex)
      .map { case (ctex, expected, got) =>
        // ctex is ordered according to the model, so we need to reorder cand according to the permutation
        val candReorg = candPerm.m2c.map(cand.params)
        Ctex(candReorg.zip(ctex).toMap, expected, got)
      }
  }
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Pruning of sub function matching

  private case class PrunedSubFnsMatching(passed: Seq[SubFnsMatching], invalidPairs: Set[(Identifier, Identifier, ArgPermutation)])

  private def pruneSubFnsMatching(matching: Seq[SubFnsMatching]): PrunedSubFnsMatching = {
    def loop(matching: Seq[SubFnsMatching],
             acc: Seq[SubFnsMatching],
             invalidPairs: Set[(Identifier, Identifier, ArgPermutation)]): (Seq[SubFnsMatching], Set[(Identifier, Identifier, ArgPermutation)]) = matching match {
      case Seq() => (acc, invalidPairs)
      case m +: rest =>
        // If this matching contains pairs that are invalid, skip it and go to the next
        val mpairs = m.pairs.map { case ((mod, cand), perm) => (mod, cand, perm) }.toSet
        if (mpairs.intersect(invalidPairs).nonEmpty) loop(rest, acc, invalidPairs)
        else {
          // Otherwise, try to falsify this matching by finding an invalid pair
          val newInvPair = findMap(m.pairs.toSeq) { case ((mod, cand), perm) =>
            evalCheckCtexOnly(symbols.functions(mod), symbols.functions(cand), perm)
              .map(_ => (mod, cand, perm))
          }
          newInvPair match {
            case Some((mod, cand, perm)) =>
              // A fine addition to my collection of invalid pairs
              loop(rest, acc, invalidPairs + ((mod, cand, perm)))
            case None =>
              // This matching passed the pruning, add it to the result
              loop(rest, acc :+ m, invalidPairs)
          }
        }
    }
    val startInvPairs = invalidFunctionsPairsCache.toSet
    val (remaining, invalidPairs) = loop(matching, Seq.empty, startInvPairs)
    val extra = invalidPairs -- startInvPairs
    invalidFunctionsPairsCache ++= extra
    PrunedSubFnsMatching(remaining, extra)
  }
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Generation of all possible matching for model and candidate subfunctions

  // Note: does not perform pruning by counter-example evaluation
  private def allSubFnsMatches(model: Identifier, cand: Identifier): Seq[SubFnsMatching] = {
    import math.Ordering.Implicits.seqOrdering
    // Get all the (non-library) function transitive calls in the body of fd - excluding fd itself
    def getTransitiveCalls(f: Identifier): Set[FunDef] =
      symbols.transitiveCallees(f).filter(_ != f).map(symbols.functions(_))
        .filter(!_.flags.exists(_.name == "library"))

    def compatibleRetTpe(mod: FunDef, cand: FunDef): Boolean = {
      // To check return type, substitute all cand tparams by mod's
      val substMap = cand.tparams.zip(mod.tparams).map { case (tpd2, tpd1) => tpd2.tp -> (tpd1.tp: Type) }.toMap
      mod.returnType == typeOps.instantiateType(cand.returnType, substMap)
    }

    // Ensure that we do *not* match `choose` functions created from `choose` expressions.
    // If we were to match them, we would unveil `choose` expressions which we don't want to do
    // because these must remain hidden behind their `choose` expression counterpart.
    def isChooseStub(fd: FunDef): Boolean = fd.id.name == "choose" && (fd.fullBody match {
      case Choose(_, _) => true
      case _ => false
    })

    val modSubs = getTransitiveCalls(model)
    val candSubs = getTransitiveCalls(cand)
    // All pairs model-candidate subfns that with compatible signature modulo arg permutation
    val allValidPairs = for {
      ms <- modSubs
      if !isChooseStub(ms)
      cs <- candSubs
      if !isChooseStub(cs)
      // If allArgsPermutations returns empty, then this ms-cs pairs is not compatible
      argPerm <- allArgsPermutations(ms.params, ms.tparams, cs.params, cs.tparams)
      if compatibleRetTpe(ms, cs) // still needs to check for return type, as allArgsPermutations is only about the arguments
    } yield (ms.id, cs.id, argPerm)

    val allValidPairs2: Map[(Identifier, Identifier), Seq[ArgPermutation]] =
      allValidPairs.groupMap { case (ms, cs, _) => (ms, cs) }(_._3)
        .view.mapValues(_.toSeq.sortBy(_.m2c)).toMap // Sort the arg. permutation to ensure deterministic traversal

    // Matches between identifiers, with all possible permutation
    val resMatching0: Set[Matching[Identifier, Seq[ArgPermutation]]] = allMatching(allValidPairs2)
    if (resMatching0.isEmpty) return Seq.empty

    // Sort the results to ensure deterministic traversal and picking
    val resMatching1: Seq[Matching[Identifier, Seq[ArgPermutation]]] = resMatching0.toSeq.sortBy(_.pairs.keys.toSeq)

    // To avoid explosion of all possible function matching with all combination of argument permutation,
    // we distribute the number of maximum permutations per function matching s.t. we don't exceed maxMatchingPermutation
    def distributePermutations(budget: Int, perms: Seq[Int]): Seq[Int] = {
      type Ix = Int
      def helper(budget: Int, remaining: Map[Ix, Int], distributed: Map[Ix, Int]): Seq[Int] = {
        assert(budget >= 0)
        assert(remaining.forall(_._2 > 0))
        assert(distributed.forall(_._2 >= 0))
        if (remaining.isEmpty) distributed.toSeq.sortBy(_._1).map(_._2)
        else {
          val toDistr0 = budget / remaining.size
          if (toDistr0 == 0) {
            val toInc = remaining.keys.toSeq.sorted.take(budget % remaining.size)
            val distr2 = distributed ++ toInc.map(ix => ix -> (distributed(ix) + 1)).toMap
            distr2.toSeq.sortBy(_._1).map(_._2)
          } else {
            val toDistr = math.min(toDistr0, remaining.values.min)
            val rem2 = remaining.view.mapValues(_ - toDistr).filter(_._2 != 0).toMap
            val distr2 = distributed ++ remaining.keys.map(ix => ix -> (distributed(ix) + toDistr)).toMap
            val res = helper(budget - toDistr * remaining.size, rem2, distr2)
            res
          }
        }
      }
      helper(budget, perms.zipWithIndex.map { case (p, ix) => ix -> p }.toMap, perms.indices.map(_ -> 0).toMap)
    }
    val nbPermutations = resMatching1.map(_.pairs.map(_._2.size).product)
    val nbPermutationsDistr = distributePermutations(maxMatchingPermutation, nbPermutations)

    // We want a Matching[Identifier, ArgPermutation] and not a Seq[ArgPermutation] as "edge data"
    def allPermutation(m: Matching[Identifier, Seq[ArgPermutation]], maxPerms: Int): Seq[Matching[Identifier, ArgPermutation]] = {
      val tuples = m.pairs.toSeq.map { case ((mod, cand), perms) =>
        perms.map(perm => (mod, cand, perm))
      }
      cartesianProduct(tuples).take(maxPerms).map { pairs =>
        val pairs2 = pairs.map { case (mod, cand, perm) => (mod, cand) -> perm }.toMap
        assert(m.pairs.keySet == pairs2.keySet, "Cartesian product is hard")
        assert(pairs2.forall { case ((mod, cand), perm) => m.pairs((mod, cand)).contains(perm) }, "Making sense of all of this is hard")
        Matching(pairs2)
      }.toSeq
    }

    val res = resMatching1.zipWithIndex.flatMap { case (m, ix) => allPermutation(m, nbPermutationsDistr(ix)) }
    assert(res.size <= maxMatchingPermutation, "oh no, I lied :(")
    res
  }

  // Note: tparams are not checked for permutation
  private def allArgsPermutations(params1: Seq[ValDef], tparams1: Seq[TypeParameterDef],
                                  params2: Seq[ValDef], tparams2: Seq[TypeParameterDef]): Set[ArgPermutation] =
    EquivalenceChecker.allArgsPermutations(trees)(params1, tparams1, params2, tparams2)
  //endregion

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Miscellaneous

  private def addCtex(ctex: Seq[Expr]): Unit = {
    val currNbCtex = ctexsDb.map(_._2.size).sum
    if (currNbCtex < maxCtex) {
      val sig = UnordSig(ctex.groupMapReduce(_.getType(using symbols))(_ => 1)(_ + _))
      val unordCtex = UnordCtex(ctex.groupBy(_.getType(using symbols)))
      val arr = ctexsDb.getOrElseUpdate(sig, mutable.Set.empty)
      arr += unordCtex
    }
  }

  // Note: order enforced
  private def areSignaturesCompatible(fd1: FunDef, fd2: FunDef): Boolean =
    EquivalenceChecker.areSignaturesCompatible(trees)(fd1, fd2)

  private def areSignaturesCompatibleModuloPerm(fd1: FunDef, fd2: FunDef, argPerm: ArgPermutation): Boolean =
    EquivalenceChecker.areSignaturesCompatibleModuloPerm(trees)(fd1, fd2, argPerm)

  // deps refers to equivalence lemma, proofs and sublemmas.
  private def extractSolvingInfo(analysis: VerificationAnalysis, cand: Identifier, deps: Seq[Identifier]): SolvingInfo = {
    val all = (cand +: deps).toSet
    val (time, solvers, fromCache, trivial) = analysis.vrs.foldLeft((0L, Set.empty[String], true, true)) {
      case ((time, solvers, fromCache, trivial), (vc, vcRes)) if all(vc.fid) =>
        (time + vcRes.time.getOrElse(0L), solvers ++ vcRes.solverName.toSet, fromCache && vcRes.isValidFromCache, trivial && vcRes.isTrivial)
      case (acc, _) => acc
    }
    val solver = if (solvers.isEmpty) None else Some(solvers.mkString(", "))
    SolvingInfo(time, solver, fromCache, trivial)
  }

  // Order the ctex arguments according to the signature of `fn`, instantiate type parameters to BigInt and fill missing values with default values
  private def ctexOrderedArguments(fn: Identifier, prog: StainlessProgram)(ctex: Map[prog.trees.ValDef, prog.trees.Expr]): Option[Seq[Expr]] = {
    // `fn` may be a sublemma, etc. that do not originally belong to `symbols`, we pick the symbols of prog which will definitely contain it
    val fd = prog.symbols.functions(fn)
    val params = fd.params.map(prog2self(prog)(_))
    val tparams = fd.tparams.map(prog2self(prog)(_))
    val subst = TyParamSubst(IntegerType(), i => Some(IntegerLiteral(i)))
    tryRemapCtex(params, tparams, prog)(ctex)(using subst, context) match {
      case RemappedCtex.Success(args, _) => Some(args)
      case _ => None
    }
  }

  private def findMap[A, B](as: Seq[A])(f: A => Option[B]): Option[B] =
    if (as.isEmpty) None
    else f(as.head).orElse(findMap(as.tail)(f))

  // Adapted from inox.utils.SeqUtils, but lazy
  private type Tuple[T] = Seq[T]

  private def cartesianProduct[T](seqs: Tuple[Seq[T]]): Iterator[Tuple[T]] = {
    val sizes = seqs.map(_.size)
    val max = sizes.product

    for (i <- (0 until max).iterator) yield {
      var c = i
      var sel = -1
      for (s <- sizes) yield {
        val index = c % s
        c = c / s
        sel += 1
        seqs(sel)(index)
      }
    }
  }
  //endregion
}

object EquivalenceChecker {
  val defaultN = 3
  val defaultInitScore = 200
  val defaultMaxMatchingPermutation = 16
  val defaultMaxCtex = 1024
  val defaultMaxStepsEval = 512

  type Path = Seq[String]

  sealed trait Creation {
    val trees: Trees
    val symbols: trees.Symbols
  }
  object Creation {
    sealed trait Success extends Creation { self =>
      val equivChker: EquivalenceChecker{val trees: self.trees.type; val symbols: self.symbols.type}
    }
    sealed trait Failure(val reason: FailureReason) extends Creation
  }

  enum FailureReason {
    case IllFormedTests(invalid: Map[Identifier, TestExtractionFailure])
    case NoModels
    case NoFunctions
    case ModelsSignatureMismatch(m1: Identifier, m2: Identifier)
    case OverlappingModelsAndFunctions(overlapping: Set[Identifier])
    case MultipleNormFunctions(norms: Set[Identifier])
    case NormSignatureMismatch(norm: Identifier)
    case IllegalHyperparameterValue(details: String)
  }

  enum TestExtractionFailure {
    case ModelTakesNoArg // i.e. the model function does not take any argument, how can we possibly feed any data?
    case ReturnTypeMismatch
    case UnknownExpr
    case NoData
    case UnificationFailure
  }

  def tryCreate(ts: Trees)(syms: ts.Symbols)(using context: inox.Context): Creation {
    val trees: ts.type
    val symbols: syms.type
  } = {
    val pathsOptCandidates: Option[Seq[Path]] = context.options.findOption(equivchk.optCompareFuns) map { functions =>
      functions map CheckFilter.fullNameToPath
    }
    val pathsOptModels: Option[Seq[Path]] = context.options.findOption(equivchk.optModels) map { functions =>
      functions map CheckFilter.fullNameToPath
    }
    val pathsOptNorm: Option[Seq[Path]] =
      Some(Seq(context.options.findOptionOrDefault(equivchk.optNorm)).map(CheckFilter.fullNameToPath))

    def isNorm(fid: Identifier): Boolean = indexOfPath(pathsOptNorm, fid).isDefined

    def failure(reason: FailureReason) = {
      class FailureImpl(override val trees: ts.type, override val symbols: syms.type) extends Creation.Failure(reason)
      new FailureImpl(ts, syms)
    }

    val n = context.options.findOptionOrDefault(optN)
    if (n <= 0) {
      return failure(FailureReason.IllegalHyperparameterValue(s"${optN.name} must be strictly positive"))
    }
    val initScore = context.options.findOptionOrDefault(optInitScore)
    // If you want to give negative score to your models, sure, do so!

    val maxPerm = context.options.findOptionOrDefault(optMaxPerm)
    if (maxPerm <= 0) {
      return failure(FailureReason.IllegalHyperparameterValue(s"${optMaxPerm.name} must be strictly positive"))
    }

    val maxCtex = context.options.findOptionOrDefault(optMaxCtex)
    if (maxCtex <= 0) {
      return failure(FailureReason.IllegalHyperparameterValue(s"${optMaxCtex.name} must be strictly positive"))
    }

    val models = syms.functions.values.flatMap { fd =>
      if (fd.flags.exists(_.name == "library")) None
      else indexOfPath(pathsOptModels, fd.id).map(_ -> fd.id)
    }.toSeq.distinct.sorted.map(_._2)

    val functions = syms.functions.values.flatMap { fd =>
      if (fd.flags.exists(_.name == "library")) None
      else indexOfPath(pathsOptCandidates, fd.id).map(_ -> fd.id)
    }.toSeq.distinct.sorted.map(_._2)

    if (models.isEmpty) {
      return failure(FailureReason.NoModels)
    }
    if (functions.isEmpty) {
      return failure(FailureReason.NoFunctions)
    }

    val overlapping = models.toSet.intersect(functions.toSet)
    if (overlapping.nonEmpty) {
      return failure(FailureReason.OverlappingModelsAndFunctions(overlapping))
    }

    validateModelsSignature(ts)(syms, models) match {
      case Some((m1, m2)) =>
        return failure(FailureReason.ModelsSignatureMismatch(m1, m2))
      case None => ()
    }

    val norm = {
      val allNorms = syms.functions.values.filter(elem => isNorm(elem.id)).map(_.id).toSet
      if (allNorms.size > 1) return failure(FailureReason.MultipleNormFunctions(allNorms))
      else if (allNorms.isEmpty) None
      else {
        val norm = allNorms.head
        if (checkArgsNorm(ts)(syms, models.head, norm)) Some(norm)
        else return failure(FailureReason.NormSignatureMismatch(norm))
      }
    }

    val (testsNok0, testsOk0) = syms.functions.values.filter(_.flags.exists(elem => elem.name == "mkTest")).partitionMap { fd =>
      extractTest(ts)(syms, models.head, fd.id) match {
        case success: ExtractedTest.Success =>
          Right(fd.id -> (success.samples.asInstanceOf[Seq[ts.Expr]], success.instTparams.asInstanceOf[Seq[ts.Type]]))
        case ExtractedTest.Failure(reason) => Left(fd.id -> reason)
      }
    }
    val testsNok = testsNok0.toMap
    if (testsNok.nonEmpty) {
      return failure(FailureReason.IllFormedTests(testsNok))
    }
    val testsOk = testsOk0.toMap

    class EquivalenceCheckerImpl(override val trees: ts.type, override val symbols: syms.type)
      extends EquivalenceChecker(ts, models, functions, norm, n, initScore, maxPerm, maxCtex, defaultMaxStepsEval)(testsOk, symbols)
    val ec = new EquivalenceCheckerImpl(ts, syms)
    class SuccessImpl(override val trees: ts.type, override val symbols: syms.type, override val equivChker: ec.type) extends Creation.Success
    new SuccessImpl(ts, syms, ec)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  private def validateModelsSignature(ts: Trees)(syms: ts.Symbols, models: Seq[Identifier]): Option[(Identifier, Identifier)] = {
    import ts._
    val unordPairs = for {
      (m1, i1) <- models.zipWithIndex
      m2 <- models.drop(i1 + 1)
    } yield (m1, m2)
    unordPairs.find { case (m1, m2) => !areSignaturesCompatible(ts)(syms.functions(m1), syms.functions(m2)) }
  }

  private def areSignaturesCompatible(ts: Trees)(fd1: ts.FunDef, fd2: ts.FunDef): Boolean =
    areSignaturesCompatibleModuloPerm(ts)(fd1.params, fd1.tparams, fd1.returnType, fd2.params, fd2.tparams, fd2.returnType, ArgPermutation(fd1.params.indices))

  private def areSignaturesCompatibleModuloPerm(ts: Trees)(fd1: ts.FunDef, fd2: ts.FunDef, perm: ArgPermutation): Boolean =
    areSignaturesCompatibleModuloPerm(ts)(fd1.params, fd1.tparams, fd1.returnType, fd2.params, fd2.tparams, fd2.returnType, perm)

  private def areSignaturesCompatibleModuloPerm(ts: Trees)(
    params1: Seq[ts.ValDef], tparams1: Seq[ts.TypeParameterDef], retTpe1: ts.Type,
    params2: Seq[ts.ValDef], tparams2: Seq[ts.TypeParameterDef], retTpe2: ts.Type,
    perm: ArgPermutation
  ): Boolean = {
    import ts._
    // To check signature, substitute all t2 tparams by t1's
    val substMap = tparams2.zip(tparams1).map { case (tpd2, tpd1) => tpd2.tp -> (tpd1.tp: Type) }.toMap

    def tpeOk(t1: Type, t2: Type): Boolean = t1 == typeOps.instantiateType(t2, substMap)

    params1.size == params2.size && tparams1.size == tparams2.size &&
      params1.zip(perm.m2c.map(params2)).forall { case (vd1, vd2) => tpeOk(vd1.tpe, vd2.tpe) } &&
      tpeOk(retTpe1, retTpe2)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  case class ArgPermutation(m2c: Seq[Int]) {
    require(m2c.toSet == m2c.indices.toSet, "Permutations are hard")

    def reverse: ArgPermutation =
    // zipWithIndex will give (candidate ix, model ix)
      ArgPermutation(m2c.zipWithIndex.sortBy(_._1).map(_._2))
  }

  // All pairs of a matching in pairs.keySet, the "A" is extra information
  case class Matching[N, A](pairs: Map[(N, N), A]) {
    require(pairs.nonEmpty)
    require(isMatching(pairs.keySet), "Matching is hard")
  }

  // Note: tparams are not checked for permutation
  private def allArgsPermutations(ts: Trees)(vdparams1: Seq[ts.ValDef], tparams1: Seq[ts.TypeParameterDef],
                                             vdparams2: Seq[ts.ValDef], tparams2: Seq[ts.TypeParameterDef]): Set[ArgPermutation] = {
    import ts._
    if (vdparams1.size != vdparams2.size || tparams1.size != tparams2.size) return Set.empty

    val params1 = vdparams1.map(_.tpe)
    val params2 = vdparams2.map(_.tpe)

    def multiplicity(tps: Seq[Type]): Map[Type, Int] = tps.groupMapReduce(identity)(_ => 1)(_ + _)

    // Substitute all t2 tparams by t1's
    val substMap = tparams2.zip(tparams1).map { case (tpd2, tpd1) => tpd2.tp -> (tpd1.tp: Type) }.toMap

    val params2Substed = params2.map(typeOps.instantiateType(_, substMap))
    val p1Mult = multiplicity(params1)
    val p2Mult = multiplicity(params2Substed)
    if (p1Mult != p2Mult) return Set.empty

    // Type -> list of their index in params2
    val ixsTpe2 = params2Substed.zipWithIndex.groupMap(_._1)(_._2)
    // A graph whose nodes are the index of the arguments for params1 and params2
    // There is an edge iff the types are the same
    val edges = params1.zipWithIndex.flatMap { case (tp, ix1) =>
      ixsTpe2(tp).map(ix2 => ix1 -> ix2)
    }.toSet
    // Sanity check: must of the same type
    assert(edges.forall { case (ix1, ix2) => params1(ix1) == params2Substed(ix2) }, "Constructing a graph for matching types is hard, isn't it?")
    allMatching(edges.map(_ -> ()).toMap)
      .map(m => ArgPermutation(m.pairs.keys.toSeq.sortBy(_._1).map(_._2)))
  }

  private def isMatching[T](pairs: Set[(T, T)]): Boolean = {
    val l2rs = pairs.groupMap(_._1)(_._2)
    val r2ls = pairs.groupMap(_._2)(_._1)
    l2rs.forall(_._2.size == 1) && r2ls.forall(_._2.size == 1)
  }

  // All matching for the given edges. The "A" is extra information for the given edge (unused for matching but useful for other applications)
  private def allMatching[N, A](edges: Map[(N, N), A]): Set[Matching[N, A]] = {

    // Like Matching but without the data, which we will feed once we are done
    case class Mtching(pairs: Set[(N, N)])

    // Remove all edges touching `l` (on the left)
    def rmLeft(edges: Set[(N, N)], l: N): Set[(N, N)] =
      edges.filter { case (left, _) => left != l }

    def rmRight(edges: Set[(N, N)], r: N): Set[(N, N)] =
      edges.filter { case (_, right) => right != r }

    def rec(left: Set[N], edges: Set[(N, N)]): Set[Mtching] = {
      if (edges.isEmpty) Set.empty
      else if (isMatching(edges)) Set(Mtching(edges))
      else {
        assert(left.nonEmpty)
        val l = left.head
        val allR = edges.filter(_._1 == l).map(_._2)
        // All possible sub matching when not taking any edge from l
        val skipping = {
          val skip = rec(left.tail, rmLeft(edges, l))
          skip.flatMap { m =>
            // r's that are not matched in the sub problem are added back to the matching solution
            val unmatchedRs = allR -- m.pairs.map(_._2)
            if (unmatchedRs.isEmpty) Set(m)
            else unmatchedRs.map(r => Mtching(m.pairs + ((l, r))))
          }
        }
        val subs = allR.flatMap { r =>
          val subs = rec(left.tail, rmLeft(rmRight(edges, r), l))
          if (subs.isEmpty) Set(Mtching(Set((l, r))))
          else subs.map(m => Mtching(m.pairs + ((l, r))))
        }
        subs ++ skipping
      }
    }

    rec(edges.keySet.map(_._1), edges.keySet)
      .map(m => Matching(m.pairs.map(e => e -> edges(e)).toMap))
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  private def indexOfPath(paths: Option[Seq[Path]], fid: Identifier): Option[Int] = paths match {
    case None => None
    case Some(paths) =>
      // Support wildcard `_` as specified in the documentation.
      // A leading wildcard is always assumed.
      val path: Path = CheckFilter.fullNameToPath(CheckFilter.fixedFullName(fid))
      val ix = paths indexWhere { p =>
        if (p endsWith Seq("_")) path containsSlice p.init
        else path endsWith p
      }
      if (ix >= 0) Some(ix)
      else None
  }

  // To be compatible:
  // -norm's first n-1 params must be compatible with the model params
  // -norm return type must be compatible with return type of model
  // -norm last param must be the same as its return type (i.e. compatible with the return type of model)
  private def checkArgsNorm(ts: Trees)(symbols: ts.Symbols, model: Identifier, norm: Identifier): Boolean = {
    val m = symbols.functions(model)
    val n = symbols.functions(norm)
    n.params.nonEmpty && n.params.last.tpe == n.returnType &&
      areSignaturesCompatibleModuloPerm(ts)(m.params, m.tparams, m.returnType, n.params.init, n.tparams, n.returnType, ArgPermutation(m.params.indices))
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  private enum ExtractedTest {
    case Success(ts: Trees)(val samples: Seq[ts.Expr], val instTparams: Seq[ts.Type])
    case Failure(reason: TestExtractionFailure)
  }

  private def extractTest(ts: Trees)(syms: ts.Symbols, anyModelId: Identifier, fnId: Identifier): ExtractedTest = {
    import ts._
    given ts.Symbols = syms

    val anyModelFd = syms.functions(anyModelId)
    if (anyModelFd.params.isEmpty) {
      // Why on earth would you do that??
      return ExtractedTest.Failure(TestExtractionFailure.ModelTakesNoArg)
    }

    val fd = syms.functions(fnId)
    val elemsTpe = fd.returnType match {
      case ADTType(id: SymbolIdentifier, Seq(tp)) if id.symbol.path == Seq("stainless", "collection", "List") => tp
      case _ => return ExtractedTest.Failure(TestExtractionFailure.ReturnTypeMismatch)
    }

    def peel(e: Expr, acc: Seq[Expr]): Either[Expr, Seq[Expr]] = e match {
      case ADT(id: SymbolIdentifier, _, Seq(head, tail)) if id.symbol.path == Seq("stainless", "collection", "Cons") =>
        peel(tail, acc :+ head)
      case ADT(id: SymbolIdentifier, _, Seq()) if id.symbol.path == Seq("stainless", "collection", "Nil") =>
        Right(acc)
      case _ => Left(e)
    }

    val samples = peel(fd.fullBody, Seq.empty) match {
      case Left(_) => return ExtractedTest.Failure(TestExtractionFailure.UnknownExpr)
      case Right(Seq()) => return ExtractedTest.Failure(TestExtractionFailure.NoData)
      case Right(samplesTupled) => samplesTupled
    }

    val modelTpe = {
      if (anyModelFd.params.size == 1) anyModelFd.params.head.tpe
      else TupleType(anyModelFd.params.map(_.tpe))
    }
    val instTparams = syms.unify(elemsTpe, modelTpe, anyModelFd.tparams.map(_.tp)) match {
      case Some(mapping0) =>
        assert(mapping0.map(_._1).toSet == anyModelFd.tparams.map(_.tp).toSet)
        val mapping = mapping0.toMap
        anyModelFd.tparams.map(tpd => mapping(tpd.tp))
      case None => return ExtractedTest.Failure(TestExtractionFailure.UnificationFailure)
    }
    ExtractedTest.Success(ts)(samples, instTparams)
  }
}