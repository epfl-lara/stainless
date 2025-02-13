package stainless
package verification

import inox.utils.OffsetPosition
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import java.io.File
import scala.collection.concurrent.TrieMap

// Essentially testing the tests
class CheckFilesUtilsTest extends AnyFunSuite with Matchers {
  import CheckFilesUtils.*

  // See mkIden
  private val identifierMap: TrieMap[String, Identifier] = TrieMap()

  private val file1 = File("invalid/DummyFile.scala")
  private val check1 =
    """10:20;someFunction;precondition;valid
      |10:20;someFunction;precondition;valid
      |10:20;someFunction;precondition;invalid
      |11:20;someFunction;body assertion: inlined precondition of check;valid
      |12:20;someFunction;error: unreachable;valid
      |13:20;someFunction;class invariant: SomeClass;valid""".stripMargin

  private val file2 = File("valid/DummyFile.scala")
  private val check2 =
    """10:20;someFunction;precondition;valid
      |20:20;anotherFunction;measure decreases;valid
      |20:20;anotherFunction;measure decreases;valid
      |20:20;anotherFunction;measure decreases;valid
      |20:20;anotherFunction;measure decreases;valid
      |22:20;anotherFunction;non-negative measure;valid""".stripMargin

  private val linesByFile = Map(file1 -> check1.split("\n").toSeq, file2 -> check2.split("\n").toSeq)

  private val expected1 = Seq(
    // Occurring 3x (of one with different result), but should be fine
    VCInfo(Some(SimplePosition(10, 20, file1)), "someFunction", VCKind.Precondition, VCStatus.Valid),
    VCInfo(Some(SimplePosition(10, 20, file1)), "someFunction", VCKind.Precondition, VCStatus.Valid),
    VCInfo(Some(SimplePosition(10, 20, file1)), "someFunction", VCKind.Precondition, InvalidVC),
    VCInfo(Some(SimplePosition(11, 20, file1)), "someFunction", VCKind.AssertErr("inlined precondition of check"), VCStatus.Valid),
    VCInfo(Some(SimplePosition(12, 20, file1)), "someFunction", VCKind.Error("unreachable"), VCStatus.Valid),
    VCInfo(Some(SimplePosition(13, 20, file1)), "someFunction", ClassInvariant("SomeClass"), VCStatus.Valid),
  )
  private val expected2 = Seq(
    VCInfo(Some(SimplePosition(10, 20, file2)), "someFunction", VCKind.Precondition, VCStatus.Valid),
    // appearing 4x
    VCInfo(Some(SimplePosition(20, 20, file2)), "anotherFunction", VCKind.MeasureDecreases, VCStatus.Valid),
    VCInfo(Some(SimplePosition(20, 20, file2)), "anotherFunction", VCKind.MeasureDecreases, VCStatus.Valid),
    VCInfo(Some(SimplePosition(20, 20, file2)), "anotherFunction", VCKind.MeasureDecreases, VCStatus.Valid),
    VCInfo(Some(SimplePosition(20, 20, file2)), "anotherFunction", VCKind.MeasureDecreases, VCStatus.Valid),
    VCInfo(Some(SimplePosition(22, 20, file2)), "anotherFunction", VCKind.MeasurePositive, VCStatus.Valid),
  )

  ////////////////////////////////////////////////////////////////

  test("Parsing should work") {
    locally {
      val expected = ExpectedVCInfos(Map(file1 -> expected1))
      // The checkfile here is not relevant
      val got = parse(file1, file1, check1.split("\n").toSeq)
      got `shouldBe` Right(expected)
    }
    locally {
      val expected = ExpectedVCInfos(Map(file2 -> expected2))
      val got = parse(file2, file2, check2.split("\n").toSeq)
      got `shouldBe` Right(expected)
    }
  }

  test("checkVCResults should account for unknown origin and no occurrences") {
    // No VC with admitted
    val badVC1 =
      VCInfo(Some(SimplePosition(10, 20, file1)), "someFunction", VCKind.Precondition, VCStatus.Admitted)
    // No VC with such fn name
    val badVC2 =
      VCInfo(Some(SimplePosition(10, 20, file1)), "sorry", VCKind.Precondition, VCStatus.Valid)
    // No VC with such class invariant
    val badVC3 =
      VCInfo(Some(SimplePosition(13, 20, file1)), "someFunction", ClassInvariant("AnotherClass"), VCStatus.Valid)
    // No VC with such position
    val badVC4 =
      VCInfo(Some(SimplePosition(42, 20, file1)), "someFunction", VCKind.Precondition, VCStatus.Valid)
    val badFile = File("bad/VeryBad.scala")
    // This one is set so an unknown file, so bad VC
    val badVC5 =
      VCInfo(Some(SimplePosition(10, 20, badFile)), "someFunction", VCKind.RefinementSubtype, VCStatus.Valid)
    val badVCs = Seq(badVC1, badVC2, badVC3, badVC4, badVC5)
    // The results for this scenario is the expected VCs with bad ones
    // We shuffle the "results" - this should not impact the result (modulo ordering of errors which we handle below
    val vcResults = scala.util.Random.shuffle(badVCs ++ expected1 ++ expected2).map(mkVCWithStatus)

    val expectedVCs = ExpectedVCInfos(Map(file1 -> expected1, file2 -> expected2))
    val gotCheckResult = checkVCResults[stainless.trees.type, Unit](expectedVCs, vcResults)

    // To have an order-independant result, we use a multibag
    val (gotIncorrectVCs, gotRemaining) = gotCheckResult match {
      case Left(CheckVCFailure.IncorrectVCs(incorrect, remaining)) =>
        (incorrect.groupMapReduce(identity)(_ => 1)(_ + _), remaining)
      case _ => fail("Expected to be a Left(CheckVCFailure.IncorrectVCs(.))")
    }
    // All VCs were covered, so this must be empty
    gotRemaining `shouldBe` empty
    val expectedErrs = Seq(
      CheckFailure.NoOccurrence(badVC1),
      CheckFailure.NoOccurrence(badVC2),
      CheckFailure.NoOccurrence(badVC3),
      CheckFailure.NoOccurrence(badVC4),
      CheckFailure.UnknownOrigin(badVC5)
    ).groupMapReduce(identity)(_ => 1)(_ + _)
    gotIncorrectVCs `shouldBe` expectedErrs
  }

  test("checkVCResults should account for VCs occurring more than the number of expected occurrences") {
    val repeatedVCs = Seq(expected1(0), expected1(3), expected1(3), expected2(0))
    // The results for this scenario is the expected VCs with the `repeatedVCs` occurring more than the expected # of occurrences
    // We shuffle the "results" - this should not impact the result (modulo ordering of errors which we handle below
    val vcResultsWithIx = scala.util.Random.shuffle((repeatedVCs ++ expected1 ++ expected2).zipWithIndex)
    val vcResults = vcResultsWithIx.map(_._1).map(mkVCWithStatus)
    val expectedVCs = ExpectedVCInfos(Map(file1 -> expected1, file2 -> expected2))
    val gotCheckResult = checkVCResults[stainless.trees.type, Unit](expectedVCs, vcResults)

    // To have an order-independant result, we use a multibag
    val (gotIncorrectVCs, gotRemaining) = gotCheckResult match {
      case Left(CheckVCFailure.IncorrectVCs(incorrect, remaining)) =>
        (incorrect.groupMapReduce(identity)(_ => 1)(_ + _), remaining)
      case _ => fail("Expected to be a Left(CheckVCFailure.IncorrectVCs(.))")
    }
    // All VCs were covered, so this must be empty
    gotRemaining `shouldBe` empty
    val expectedErrs = repeatedVCs.map(vc => CheckFailure.NoOccurrence(vc)).groupMapReduce(identity)(_ => 1)(_ + _)
    gotIncorrectVCs `shouldBe` expectedErrs
  }

  test("checkVCResults should account for non-covered expected VCs") {
    // For this test, we simulate a partial cover by taking out some "expected VCs" from the expected set
    val (uncovered, covered) = scala.util.Random.shuffle(expected1 ++ expected2).splitAt(4)
    val vcResults = covered.map(mkVCWithStatus)
    val expectedVCs = ExpectedVCInfos(Map(file1 -> expected1, file2 -> expected2))
    val gotCheckResult = checkVCResults[stainless.trees.type, Unit](expectedVCs, vcResults)

    // To have an order-independant result, we use a multibag
    val expectedRemaining = uncovered.groupBy(_.pos.get.file).view.mapValues(_.groupMapReduce(identity)(_ => 1)(_ + _)).toMap
    val gotRemaining = gotCheckResult match {
      case Left(CheckVCFailure.NotCovered(remaining)) =>
        remaining.view.mapValues(_.groupMapReduce(identity)(_ => 1)(_ + _)).toMap
      case _ => fail("Expected to be a Left(CheckVCFailure.NotCovered(.))")
    }
    gotRemaining `shouldBe` expectedRemaining
  }

  test("checkVCResults should validate correct VC results") {
    val expected = ExpectedVCInfos(Map(file1 -> expected1, file2 -> expected2))
    val vcResults = (expected1 ++ expected2).map(mkVCWithStatus)
    val gotCheckResult = checkVCResults[stainless.trees.type, Unit](expected, vcResults)
    gotCheckResult `shouldBe` Right(())
  }

  ////////////////////////////////////////////////////////////////

  // For the testing purposes, we need to map a string to a unique identifier.
  // Since two different identifier must have different ids, we must use FreshIdentifier,
  // which we store in the identifierMap map
  def mkIden(str: String): Identifier = identifierMap.getOrElseUpdate(str, FreshIdentifier(str))

  def mkVCWithStatus(simplerVC: VCInfo): (VC[stainless.trees.type], VCStatus[Unit]) =
    (mkVC(simplerVC), mkVCStatus(simplerVC.vcStatus))

  def mkVCStatus(status: VCStatus[Nothing] | InvalidVC.type): VCStatus[Unit] = status match {
    case InvalidVC => VCStatus.Invalid(VCStatus.CounterExample(()))
    case other => other.asInstanceOf[VCStatus[Nothing]]
  }

  def mkVC(simplerVC: VCInfo): VC[stainless.trees.type] =
    mkVC(simplerVC.pos, simplerVC.fn, simplerVC.vcKind)

  def mkVC(pos: Option[SimplePosition], fn: String, vcKind: VCKind | ClassInvariant): VC[stainless.trees.type] = {
    val vc = VC(stainless.trees)(
      stainless.trees.BooleanLiteral(true), // unused
      mkIden(fn),
      vcKind match {
        case ClassInvariant(clsId) => VCKind.AdtInvariant(mkIden(clsId))
        case other => other.asInstanceOf[VCKind]
      },
      satisfiability = false // unused
    )

    pos.foreach { p =>
      val inoxPos = OffsetPosition(p.line, p.column, 0, p.file)
      vc.condition.setPos(inoxPos)
      vc.setPos(inoxPos)
    }
    vc
  }
}
