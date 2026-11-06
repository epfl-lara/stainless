/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import java.io.File
import java.nio.file.{Files, Path}

import scala.collection.mutable

import org.scalatest.Assertions

/** The update mode of the tests that compare their results against expected
 *  files of `frontends/benchmarks`: the golden C files of [[GenCSuite]] and the
 *  `.check` files of [[GenCSuite]], [[ExtractionSuite]] and
 *  [[verification.VerificationComponentTestSuite]].
 *
 *  When the environment variable `STAINLESS_UPDATE_EXPECTED` is set to `1` or
 *  `true`, these tests write what they obtain to the expected files that do not
 *  match it, instead of failing. The changes are then reviewed in the diff.
 */
object ExpectedFiles:

  /** Whether the tests update the expected files instead of failing when they
   *  do not match.
   */
  val updateMode: Boolean =
    sys.env.get("STAINLESS_UPDATE_EXPECTED").exists(v => v == "1" || v.equalsIgnoreCase("true"))

  /** How to update the expected files, for the messages of the tests that fail.
   */
  val updateHint: String =
    "If this change is intended, re-run with STAINLESS_UPDATE_EXPECTED=1 to update the expected file."

  /** The expected files that the tests of this run found up to date or updated.
   */
  private val settled = mutable.Set.empty[Path]

  /** The source file in `frontends/benchmarks` of the test resource `resource`.
   *
   *  The benchmarks are copied to the `it-classes` directory of the build,
   *  where the tests read them from, but the expected files must be updated in
   *  the source tree so that they can be committed. The file does not need to
   *  exist.
   */
  def sourceFile(resource: File): File =
    val path = resource.toPath.toAbsolutePath.normalize
    def ancestors(p: Path): Iterator[Path] = Iterator.iterate(p)(_.getParent).takeWhile(_ != null)
    val resourceRoot = ancestors(path)
      .find(p => Option(p.getFileName).exists(_.toString == "it-classes"))
      .getOrElse(throw IllegalArgumentException(s"$resource is not in the directory of the test resources"))
    val benchmarks = ancestors(resourceRoot)
      .map(_.resolve("frontends").resolve("benchmarks"))
      .find(Files.isDirectory(_))
      .getOrElse(throw IllegalArgumentException(s"No frontends/benchmarks directory above $resourceRoot"))
    benchmarks.resolve(resourceRoot.relativize(path)).toFile

  /** In update mode, writes the `obtained` contents to the source file of the
   *  test resource `resource`, unless the file already `matches` them.
   *
   *  Fails if another test of this run already found the file up to date or
   *  updated it, and its contents do not match the ones obtained by this test,
   *  e.g. when two solvers obtain different results for a `.check` file that
   *  they share.
   */
  def update(resource: File, obtained: String)(matches: String => Boolean): Unit =
    settle(resource, _ => obtained, matches)

  /** Like [[update]], for an expected file made of the `obtained` lines.
   *
   *  The lines are written separated by newlines, and followed by a newline
   *  unless the file already exists and does not end with one.
   */
  def updateLines(resource: File, obtained: Seq[String])(matches: Seq[String] => Boolean): Unit =
    def contents(current: Option[String]): String =
      val finalNewline = obtained.nonEmpty && current.forall(c => c.isEmpty || c.endsWith("\n"))
      obtained.mkString("\n") + (if finalNewline then "\n" else "")
    settle(resource, contents, c => matches(c.linesIterator.toSeq))

  private def settle(resource: File, obtained: Option[String] => String, matches: String => Boolean): Unit =
    assert(updateMode, "Expected files are only updated in update mode")
    val path = sourceFile(resource).toPath
    synchronized {
      val current = Option.when(Files.exists(path))(Files.readString(path))
      if !current.exists(matches) then
        if settled(path) then
          Assertions.fail(
            s"Another test of this run already found $path up to date or updated it, with results that differ " +
              "from the ones of this test. Re-run without the update mode to see the differences."
          )
        Files.writeString(path, obtained(current))
        println(s"Updated expected file $path")
      settled += path
    }
