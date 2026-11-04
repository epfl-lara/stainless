/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import stainless.evaluators.{EvaluatorComponent, EvaluatorRun, optCodeGen}
import stainless.extraction.ExtractionSummary
import stainless.extraction.utils.DebugSymbols
import stainless.extraction.xlang.trees as xt
import stainless.utils.YesNoOnly
import stainless.Utils.*

import java.io.{ByteArrayOutputStream, File, PrintStream}
import java.net.URLClassLoader
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.concurrent.Await
import scala.concurrent.duration.*
import scala.jdk.CollectionConverters.*

/** Differential test of the semantics of the `stainless.math.Unsigned` library.
  *
  * For each benchmark `X.scala` in `frontends/benchmarks/unsigned`, the sibling `X.check` lists the
  * expected results of the parameterless `testN` functions of the benchmark (`testN = value`, in the
  * order in which `main` prints them, if the benchmark has a `main`). The suite checks that the same
  * results are obtained when the program is:
  *  - verified by Stainless (with `--strict-arithmetic`, as GenC requires): the benchmarks assert their
  *    expected results, so all VCs must be valid;
  *  - evaluated by the recursive and by the code-generating evaluators;
  *  - compiled to C by GenC and run with the undefined behavior sanitizer, if the benchmark has a `main`
  *    function (which must print the results in the order of the `.check` file);
  *  - compiled by the Scala compiler against the Stainless library and run on the JVM, where the
  *    `testN` functions are called directly, the `checksN` functions must not fail, and `main` (if any)
  *    must print the same output as the C program.
  */
class UnsignedSemanticsSuite extends AnyFunSuite with inox.ResourceUtils with InputUtils with Matchers {
  import UnsignedSemanticsSuite.*

  private val benchmarks = resourceFiles("unsigned", _.endsWith(".scala"), false).map(_.getPath).sorted

  for (file <- benchmarks) {
    val name = new File(file).getName.stripSuffix(".scala")
    val checkFile = file.stripSuffix(".scala") + ".check"
    val expected = parseCheckFile(checkFile)
    lazy val mainOutput = expected.map(_._2).mkString("\n")

    test(s"unsigned/$name: verification") {
      val opts = Seq("--batched", "--solvers=smt-z3", "--timeout=30")
      val (ctx, optReport) = runMainWithArgs(Array(file) ++ opts)
      assert(ctx.reporter.errorCount == 0, "No errors")
      assert(optReport.nonEmpty, "Valid report returned by Stainless")
      assert(optReport.get.isSuccess, "Only valid VCs")
    }

    for (codegen <- Seq(false, true)) {
      val evaluator = if (codegen) "codegen evaluator" else "recursive evaluator"
      test(s"unsigned/$name: $evaluator") {
        val results = evaluate(file, expected.map(_._1), codegen)
        for ((fn, value) <- expected) {
          assert(results.contains(fn), s"$fn was not evaluated")
          assert(results(fn) == value, s"$evaluator: $fn evaluated to ${results(fn)}, expected $value")
        }
      }
    }

    test(s"unsigned/$name: JVM") {
      val program = compileForJVM(file)
      val module = program.module(name)
      for ((fn, value) <- expected) {
        val results = module.call(fn)
        assert(results.contains(value), s"JVM: $fn evaluated to ${results.mkString(" or ")}, expected $value")
      }
      for (checks <- module.methods.filter(_.startsWith("checks")).sorted) {
        module.call(checks) // must not throw
      }
      if (module.methods.contains("main")) {
        val output = module.captureOutput("main")
        assert(output == mainOutput, s"JVM: unexpected output of main:\n$output")
      }
    }

    if (hasMain(file)) {
      test(s"unsigned/$name: GenC") {
        val cFile = file.stripSuffix(".scala") + ".c"
        val outFile = file.stripSuffix(".scala") + ".out"
        runMainWithArgs(Array(file, "--genc", s"--genc-output=$cFile", "--skip-verification"))
        assert(Files.exists(Paths.get(cFile)), "GenC produced a C file")
        val (gccOutput, gccExitCode) = runCommand(s"$gccWithSanitizer $cFile -o $outFile")
        assert(gccExitCode == 0, "gcc failed with output:\n" + gccOutput.mkString("\n"))
        // Note: the exit code of the C program is meaningless, as GenC generates a `void main`.
        val (output, _) = runCommand(outFile)
        undefinedBehavior(output).foreach(ub => fail(s"GenC: the C program has undefined behavior: $ub"))
        assert(output.mkString("\n") == mainOutput, s"GenC: unexpected output of the C program:\n${output.mkString("\n")}")
      }
    }
  }

  private def hasMain(file: String): Boolean =
    Files.readString(Paths.get(file)).contains("def main()")

  /** Evaluates the parameterless functions `functions` of the benchmark `file` with the recursive
    * evaluator, or with the code-generating evaluator if `codegen` is set, and renders their values.
    */
  private def evaluate(file: String, functions: Seq[String], codegen: Boolean): Map[String, String] = {
    val options = inox.Options(Seq(
      inox.optSelectedSolvers(Set("smt-z3")),
      verification.optStrictArithmetic(false),
      frontend.optBatchedProgram(true),
      termination.optInferMeasures(false),
      termination.optCheckMeasures(YesNoOnly.No),
      optCodeGen(codegen),
    ))
    given ctx: inox.Context = stainless.TestContext(options)
    val (_, program) = loadFiles(Seq(file))
    assert(ctx.reporter.errorCount == 0, "There should be no error while loading the files")

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = ctx
      val s: xt.type = xt
      val t: xt.type = xt
    }
    val programSymbols = userFiltering.debugWithoutSummary(frontend.UserFiltering().transform)(program.symbols)._1
    programSymbols.ensureWellFormed

    val run = EvaluatorComponent.run(extraction.pipeline)
    val exSymbols = run.extract(programSymbols)._1
    exSymbols.ensureWellFormed
    assert(ctx.reporter.errorCount == 0, "There were errors during pipeline extraction")

    val fnsToEval = exSymbols.functions.keys.filter(id => functions.contains(id.name)).toSeq
    val analysis = Await.result(run.execute(fnsToEval, exSymbols, ExtractionSummary.NoSummary), Duration.Inf)

    import stainless.trees.*
    def render(e: Expr): String = e match {
      case bv: BVLiteral => bv.toBigInt.toString
      case BooleanLiteral(b) => b.toString
      case IntegerLiteral(i) => i.toString
      case other => other.toString
    }

    analysis.results.map { res =>
      val value = res.status match {
        case EvaluatorRun.NoPost(bodyValue) => render(bodyValue)
        case EvaluatorRun.PostHeld(bodyValue) => render(bodyValue)
        case other => s"<evaluation failed: $other>"
      }
      res.fd.id.name -> value
    }.toMap
  }
}

object UnsignedSemanticsSuite {

  /** Parses a `.check` file: one `name = value` entry per line, ignoring blank lines and `#` comments. */
  def parseCheckFile(path: String): Seq[(String, String)] = {
    Files.readAllLines(Paths.get(path), StandardCharsets.UTF_8).asScala.toSeq
      .map(_.trim)
      .filter(line => line.nonEmpty && !line.startsWith("#"))
      .map { line =>
        line.split("=", 2) match {
          case Array(name, value) => name.trim -> value.trim
          case _ => throw new IllegalArgumentException(s"Malformed line in $path: $line")
        }
      }
  }

  /** Where the classes of `cls` are loaded from (a directory or a jar). */
  private def codeSource(cls: Class[?]): String =
    new File(cls.getProtectionDomain.getCodeSource.getLocation.toURI).getPath

  /** The classpath needed to compile a Stainless program for the JVM: the Stainless library and the
    * Scala standard libraries (taken from where the running test loads them from). */
  private lazy val libraryClasspath: String = Seq(
    codeSource(stainless.math.Unsigned.getClass),   // the Stainless library
    codeSource(classOf[scala.util.NotGiven[?]]),    // the Scala 3 library
    codeSource(classOf[scala.Option[?]]),           // the Scala 2.13 library
  ).distinct.mkString(File.pathSeparator)

  /** A Stainless program compiled for the JVM. */
  class CompiledProgram(classesDir: Path) {
    private val loader = new URLClassLoader(Array(classesDir.toUri.toURL), getClass.getClassLoader)

    /** The top-level object `name` of the program. */
    def module(name: String): Module = {
      val cls = loader.loadClass(name + "$")
      new Module(cls, cls.getField("MODULE$").get(null))
    }
  }

  class Module(cls: Class[?], instance: AnyRef) {
    /** The parameterless methods of the object. */
    lazy val methods: Seq[String] = cls.getMethods.filter(_.getParameterCount == 0).map(_.getName).toSeq.distinct

    /** Calls the parameterless method `name` and renders its result.
      *
      * On the JVM, the unsigned types are their signed counterparts, so the result of a method returning a
      * `UByte` is a `java.lang.Byte`: an integral result is rendered both as a signed and as an unsigned value.
      * As the expected values of the `.check` file are in the range of the result type, at most one of these
      * renderings can match, and only when the result is correct.
      */
    def call(name: String): Seq[String] = {
      val result =
        try cls.getMethod(name).invoke(instance)
        catch {
          case e: java.lang.reflect.InvocationTargetException => throw e.getCause
        }
      val unsigned = result match {
        case b: java.lang.Byte => Some(java.lang.Byte.toUnsignedInt(b).toString)
        case s: java.lang.Short => Some(java.lang.Short.toUnsignedInt(s).toString)
        case i: java.lang.Integer => Some(java.lang.Integer.toUnsignedString(i))
        case l: java.lang.Long => Some(java.lang.Long.toUnsignedString(l))
        case _ => None
      }
      (String.valueOf(result) +: unsigned.toSeq).distinct
    }

    /** Calls the parameterless method `name` and returns what it printed on the standard output. */
    def captureOutput(name: String): String = {
      val out = new ByteArrayOutputStream()
      Console.withOut(new PrintStream(out, true, StandardCharsets.UTF_8)) {
        call(name)
      }
      out.toString(StandardCharsets.UTF_8).linesIterator.mkString("\n")
    }
  }

  /** Compiles the Stainless program `file` with the Scala compiler, against the Stainless library. */
  def compileForJVM(file: String): CompiledProgram = {
    val classesDir = Files.createTempDirectory("stainless-jvm")
    classesDir.toFile.deleteOnExit()
    val args = Array(
      "-d", classesDir.toString,
      "-classpath", libraryClasspath,
      "-language:experimental.qualifiedTypes",
      file,
    )
    val reporter = dotty.tools.dotc.Main.process(args)
    assert(!reporter.hasErrors, s"Compilation of $file for the JVM failed with ${reporter.errorCount} error(s)")
    new CompiledProgram(classesDir)
  }
}
