/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package semantics

import java.io.File
import java.nio.file.{Files, Paths}

import org.scalatest.funsuite.AnyFunSuite

import generated.{Semantics => S}

/** `InoxEncoder`, the last step from Stainless's trees into Inox's, against the semantics of both
  * (`proofs/semantics.md`, which extends `inox/proofs/semantics.md`).
  *
  * For the functions of some verification benchmarks that are in the fragment of the semantics,
  * each is called on random arguments that satisfy its precondition, in the program that the
  * extraction produces, with Stainless's semantics, and in the program that `InoxEncoder` makes of
  * it, with Inox's (the same evaluator, on Inox's expressions only). The encoder drops the checks
  * that Stainless proves with its VCs, so the statement assumes them: when the Stainless program
  * doesn't get stuck, both give the same result for the same fuel.
  */
class EncoderSemanticsSuite extends AnyFunSuite with InputUtils {

  private def list[A](xs: Seq[A]): S.List[A] = xs.foldRight(S.Nil(): S.List[A])(S.Cons(_, _))

  private def seq[A](l: S.List[A]): Seq[A] = l match {
    case S.Nil() => Seq()
    case S.Cons(h, t) => h +: seq(t)
  }

  private def opt[A](o: scala.Option[A]): S.Option[A] = o match {
    case scala.Some(a) => S.Some(a)
    case scala.None => S.None()
  }

  private def all[A](xs: Seq[scala.Option[A]]): scala.Option[S.List[A]] =
    if (xs.forall(_.isDefined)) scala.Some(list(xs.flatten)) else scala.None

  /** The trees of Inox or of Stainless in the semantics, if they are in its fragment. Stainless's
    * own expressions, and its integer division, only on Stainless's trees. */
  abstract class Translation {
    val t: inox.ast.Trees
    import t._

    /** Stainless's expressions that aren't Inox's, and Inox's to which it gives another meaning. */
    def extra(e: Expr)(using Symbols): scala.Option[scala.Option[S.Expr]] = scala.None

    def tpe(tp: Type): scala.Option[S.Type] = tp match {
      case IntegerType() => scala.Some(S.IntegerType())
      case BooleanType() => scala.Some(S.BooleanType())
      case UnitType() => scala.Some(S.UnitType())
      case CharType() => scala.Some(S.CharType())
      case BVType(s, w) => scala.Some(S.BVType(s, BigInt(w)))
      case TypeParameter(id, _) => scala.Some(S.TypeParameter(id))
      case TupleType(ts) => all(ts.map(tpe)).map(S.TupleType(_))
      case FunctionType(f, to) => for (a <- all(f.map(tpe)); b <- tpe(to)) yield S.FunctionType(a, b)
      case ADTType(id, tps) => all(tps.map(tpe)).map(S.ADTType(id, _))
      case _ => scala.None
    }

    def params(vds: Seq[ValDef]): scala.Option[S.List[S.Param]] =
      all(vds.map(vd => tpe(vd.tpe).map(S.Param(vd.id, _))))

    def expr(e: Expr)(using syms: Symbols): scala.Option[S.Expr] = extra(e).getOrElse {
      def es(xs: Seq[Expr]) = all(xs.map(expr))
      def two(l: Expr, r: Expr)(f: (S.Expr, S.Expr) => S.Expr) = for (a <- expr(l); b <- expr(r)) yield f(a, b)
      e match {
        case v: Variable => scala.Some(S.Variable(v.id))
        case IntegerLiteral(i) => scala.Some(S.IntegerLiteral(i))
        case BooleanLiteral(b) => scala.Some(S.BooleanLiteral(b))
        case UnitLiteral() => scala.Some(S.UnitLiteral())
        case CharLiteral(c) => scala.Some(S.CharLiteral(BigInt(c.toInt)))
        case bv: BVLiteral =>
          scala.Some(S.BVLiteral(bv.signed, BigInt(bv.size), bv.value.foldLeft(BigInt(0))((acc, i) => acc.setBit(i - 1))))
        case Let(vd, v, b) => two(v, b)(S.Let(vd.id, _, _))
        case IfExpr(c, a, b) => for (x <- expr(c); y <- expr(a); z <- expr(b)) yield S.IfExpr(x, y, z)
        case Assume(p, b) => two(p, b)(S.Assume(_, _))
        case FunctionInvocation(id, tps, args) =>
          for (ts <- all(tps.map(tpe)); as <- es(args)) yield S.FunctionInvocation(id, ts, as)
        case ADT(id, tps, args) => for (ts <- all(tps.map(tpe)); as <- es(args)) yield S.ADT(id, ts, as)
        case IsConstructor(a, id) => expr(a).map(S.IsConstructor(_, id))
        case ADTSelector(a, id) => expr(a).map(S.ADTSelector(_, id))
        case Equals(a, b) => two(a, b)(S.Equals(_, _))
        case And(xs) => es(xs).map(S.And(_))
        case Or(xs) => es(xs).map(S.Or(_))
        case Implies(a, b) => two(a, b)(S.Implies(_, _))
        case Not(a) => expr(a).map(S.Not(_))
        case Plus(a, b) => two(a, b)(S.Plus(_, _))
        case Minus(a, b) => two(a, b)(S.Minus(_, _))
        case UMinus(a) => expr(a).map(S.UMinus(_))
        case Times(a, b) => two(a, b)(S.Times(_, _))
        case Division(a, b) => two(a, b)(S.Division(_, _))
        case Remainder(a, b) => two(a, b)(S.Remainder(_, _))
        case Modulo(a, b) => two(a, b)(S.Modulo(_, _))
        case LessThan(a, b) => two(a, b)(S.LessThan(_, _))
        case GreaterThan(a, b) => two(a, b)(S.GreaterThan(_, _))
        case LessEquals(a, b) => two(a, b)(S.LessEquals(_, _))
        case GreaterEquals(a, b) => two(a, b)(S.GreaterEquals(_, _))
        case Tuple(xs) => es(xs).map(S.Tuple(_))
        case TupleSelect(a, i) => expr(a).map(S.TupleSelect(_, BigInt(i)))
        case Lambda(ps, b) => for (p <- params(ps); x <- expr(b)) yield S.Lambda(p, x)
        case Application(f, args) => for (g <- expr(f); as <- es(args)) yield S.Application(g, as)
        case _ => scala.None
      }
    }

    /** The functions in the fragment, each with the functions it calls. */
    def functions(using syms: Symbols): Map[Identifier, S.FunDef] =
      syms.functions.values.flatMap { fd =>
        expr(fd.fullBody).map(b => fd.id -> S.FunDef(fd.id, list(fd.tparams.map(_.id)), list(fd.params.map(_.id)), b))
      }.toMap

    def program(fs: Map[Identifier, S.FunDef])(using syms: Symbols): S.Program = S.Program(
      list(fs.values.toSeq),
      list(syms.constructors.values.toSeq.map(c => S.Constructor(c.id, c.sort,
        list(c.fields.map(vd => S.Param(vd.id, tpe(vd.tpe).getOrElse(S.UnitType()))))))),
      list(syms.sorts.values.toSeq.map(s => S.Sort(s.id, list(s.tparams.map(_.id)), opt(s.invariant.map(_.id))))),
      S.Nil(),
      S.NoFunctionEquality())
  }

  object Inox extends Translation {
    val t: inox.trees.type = inox.trees
  }

  object Stainless extends Translation {
    val t: stainless.trees.type = stainless.trees
    import t._

    /** Whether integer division is the JVM's, as in Stainless; only the mutation test reads it as
      * Inox's, to show that the comparison catches a wrong semantics. */
    var jvmDivision = true

    private def binder(b: scala.Option[ValDef]): S.Option[inox.Identifier] = opt(b.map(_.id))

    private def pattern(p: Pattern)(using Symbols): scala.Option[S.Pattern] = p match {
      case WildcardPattern(b) => scala.Some(S.WildcardPattern(binder(b)))
      case ADTPattern(b, id, _, subs) => all(subs.map(pattern)).map(S.ADTPattern(binder(b), id, _))
      case TuplePattern(b, subs) => all(subs.map(pattern)).map(S.TuplePattern(binder(b), _))
      case LiteralPattern(b, lit) => expr(lit).map(S.LiteralPattern(binder(b), _))
      case _ => scala.None
    }

    override def extra(e: Expr)(using Symbols): scala.Option[scala.Option[S.Expr]] = e match {
      case Require(p, b) => scala.Some(for (x <- expr(p); y <- expr(b)) yield S.Require(x, y))
      case Assert(p, _, b) => scala.Some(for (x <- expr(p); y <- expr(b)) yield S.Assert(x, y))
      case Ensuring(b, Lambda(Seq(res), post)) =>
        scala.Some(for (x <- expr(b); y <- expr(post)) yield S.Ensuring(x, res.id, y))
      case MatchExpr(scrut, cases) =>
        val cs = cases.map { case MatchCase(p, g, rhs) =>
          for (pp <- pattern(p); gg <- g.map(expr) match {
                 case scala.Some(scala.None) => scala.None
                 case other => scala.Some(opt(other.flatten))
               }; r <- expr(rhs)) yield S.MatchCase(pp, gg, r)
        }
        scala.Some(for (s <- expr(scrut); c <- all(cs)) yield S.MatchExpr(s, c))
      case Division(a, b) if jvmDivision && a.getType == IntegerType() =>
        scala.Some(for (x <- expr(a); y <- expr(b)) yield S.JVMDivision(x, y))
      case Remainder(a, b) if jvmDivision && a.getType == IntegerType() =>
        scala.Some(for (x <- expr(a); y <- expr(b)) yield S.JVMRemainder(x, y))
      // Stainless's `error` and `???` are checked unreachable, which this fragment doesn't cover yet.
      case _: Error | _: Choose | _: NoTree => scala.Some(scala.None)
      case Annotated(b, _) => scala.Some(expr(b))
      case Decreases(_, b) => scala.Some(expr(b))
      case _ => scala.None
    }
  }

  /** The generated evaluator, without quantifiers: the benchmarks' functions don't need them. */
  final class Unsupported extends Exception

  val fuel = BigInt(40)

  object Sem extends S.Evaluator {
    def forall_result(P: S.Program, fuel: BigInt, env: S.Env, params: S.List[S.Param], body: S.Expr): S.Result[S.Value] =
      throw Unsupported()
    def holds(P: S.Program, env: S.Env, prop: S.Expr): Boolean = eval(P, EncoderSemanticsSuite.this.fuel, env, prop) == S.Ok(S.BoolV(true))
    def invariant_holds(P: S.Program, f: inox.Identifier, args: S.List[S.Type], tenv: S.List[S.TypeBinding], v: S.Value): Boolean =
      call(P, EncoderSemanticsSuite.this.fuel, f, args, tenv, S.Cons(v, S.Nil())) == S.Ok(S.BoolV(true))
    def function_has_type(P: S.Program, env: S.Env, f: S.Value, from: S.List[S.Type], to: S.Type): Boolean = throw Unsupported()
    def pi_has_type(P: S.Program, env: S.Env, f: S.Value, ps: S.List[S.Param], to: S.Type): Boolean = throw Unsupported()
    def closures_equal(P: S.Program, f: S.Value, g: S.Value): Boolean = throw Unsupported()
  }

  /** Values equal up to closures, whose bodies the encoder changes. */
  private def same(a: S.Result[S.Value], b: S.Result[S.Value]): Boolean = (a, b) match {
    case (S.Ok(x), S.Ok(y)) => sameValue(x, y)
    case _ => a == b
  }

  private def sameValue(a: S.Value, b: S.Value): Boolean = (a, b) match {
    case (_: S.ClosureV, _: S.ClosureV) => true
    case (S.TupleV(xs), S.TupleV(ys)) => sameValues(xs, ys)
    case (S.ADTV(c, xs), S.ADTV(d, ys)) => c == d && sameValues(xs, ys)
    case _ => a == b
  }

  private def sameValues(xs: S.List[S.Value], ys: S.List[S.Value]): Boolean =
    seq(xs).size == seq(ys).size && seq(xs).zip(seq(ys)).forall(sameValue(_, _))

  /** A small value of type `tp`, as an expression of Stainless's trees. */
  private def value(tp: stainless.trees.Type, depth: Int, rnd: scala.util.Random)
                   (using syms: stainless.trees.Symbols): scala.Option[stainless.trees.Expr] = {
    import stainless.trees._
    tp match {
      case IntegerType() => scala.Some(IntegerLiteral(Seq(-17, -7, -3, -2, -1, 0, 1, 2, 3, 5, 100)(rnd.nextInt(11))))
      case BooleanType() => scala.Some(BooleanLiteral(rnd.nextBoolean()))
      case UnitType() => scala.Some(UnitLiteral())
      case BVType(s, w) =>
        val v = Seq(BigInt(0), BigInt(1), BigInt(-1), BigInt(7), BigInt(-100))(rnd.nextInt(5))
        scala.Some(BVLiteral(s, if (s) v else v.abs, w))
      case TupleType(ts) =>
        val vs = ts.map(value(_, depth - 1, rnd))
        if (vs.forall(_.isDefined)) scala.Some(Tuple(vs.flatten)) else scala.None
      case adt: ADTType if depth > -3 =>
        val sort = adt.getSort
        val ctors = sort.constructors
        val leaves = ctors.filter(_.fields.forall(f => f.tpe != adt))
        val pool = if (depth <= 0 && leaves.nonEmpty) leaves else ctors
        val c = pool(rnd.nextInt(pool.size))
        val args = c.fields.map(f => value(f.tpe, depth - 1, rnd))
        if (args.forall(_.isDefined)) scala.Some(ADT(c.id, adt.tps, args.flatten)) else scala.None
      case _ => scala.None
    }
  }

  enum Outcome {
    case Agree, SourceStuck, Skipped
    case Differ(msg: String)
  }

  /** The benchmarks to run on; `-Dsemantics-files=a.scala,b.scala` names others, relative to
    * `frontends/benchmarks`. */
  private val files: Seq[String] = sys.props.get("semantics-files").map(_.split(",").toSeq).getOrElse(Seq(
    "verification/valid/BinarySearch.scala",
    "verification/valid/BitsTricks.scala",
    "verification/valid/Heaps.scala",
    "verification/valid/InsertionSort.scala",
    "verification/valid/ListOperations.scala",
    "verification/valid/MergeSort.scala",
    "verification/valid/Peano.scala",
    "verification/valid/NNF.scala",
    "verification/valid/PropositionalLogic.scala",
    "verification/valid/Justify.scala",
    "verification/valid/RedBlackTree.scala",
    "verification/valid/SearchLinkedList.scala",
    "verification/valid/BigIntRing.scala",
    "verification/valid/ParBalance.scala",
    "verification/valid/AmortizedQueue.scala",
    "verification/valid/AssociativeList.scala",
  ))

  private val inputsPerFunction = sys.props.get("semantics-inputs").map(_.toInt).getOrElse(30)

  test("The generated evaluator is up to date with proofs/semantics.md") {
    assert(Codegen.scala == Files.readString(Paths.get(Codegen.scalaOutput)),
      "the generated evaluator is out of date: run `sbt stainless-proofs/run`")
  }

  private val benchmarks = Paths.get("..", "frontends", "benchmarks")

  for (file <- files) test(s"InoxEncoder preserves the meaning of $file") {
    val path = benchmarks.resolve(file)
    assume(Files.exists(path), s"no benchmark $path")
    val (summary, failures) = compare(Seq(path.toAbsolutePath.toString), file.hashCode)
    info(summary)
    assert(failures.isEmpty, failures.distinct.take(10).mkString("\n"))
  }

  /** Negative divisors and dividends, guards, literal patterns, and contracts that fail. */
  private val sample = """|import stainless.lang._
                          |
                          |object Sample {
                          |  sealed abstract class Shape
                          |  case class Square(side: BigInt) extends Shape
                          |  case class Rect(w: BigInt, h: BigInt) extends Shape
                          |  case object Empty extends Shape
                          |
                          |  def quot(x: BigInt, y: BigInt): BigInt = {
                          |    require(y != 0)
                          |    x / y
                          |  }
                          |
                          |  def rem(x: BigInt, y: BigInt): BigInt = {
                          |    require(y != 0)
                          |    x % y
                          |  } ensuring (r => (if (x >= 0) r >= 0 else r <= 0) && r * r < y * y)
                          |
                          |  def halfArea(s: Shape): BigInt = s match {
                          |    case Square(a) if a < 0 => 0
                          |    case Square(a) => a * a / 2
                          |    case Rect(w, h) => (w * h) / 2
                          |    case Empty => 0
                          |  }
                          |
                          |  def digit(x: BigInt): BigInt = (x % 10) match {
                          |    case 0 => 10
                          |    case d => d
                          |  }
                          |
                          |  def wrong(x: BigInt): BigInt = {
                          |    assert(x / 2 * 2 == x)
                          |    x / 2
                          |  } ensuring (r => r >= 0)
                          |
                          |  def callsWrong(x: BigInt): BigInt = wrong(x) + 1
                          |}
                          |""".stripMargin

  private def sampleFile: String = {
    val f = File.createTempFile("Sample", ".scala")
    f.deleteOnExit()
    Files.writeString(f.toPath, sample)
    f.getAbsolutePath
  }

  test("InoxEncoder preserves the meaning of integer division, matches and contracts") {
    val (summary, failures) = compare(Seq(sampleFile), 1)
    info(summary)
    assert(failures.isEmpty, failures.distinct.take(10).mkString("\n"))
    assert(summary.contains(" agree, ") && !summary.contains(" 0 where Stainless is stuck"), summary)
  }

  test("Reading Stainless's division as Inox's makes the comparison fail") {
    Stainless.jvmDivision = false
    val failures = try compare(Seq(sampleFile), 1)._2 finally Stainless.jvmDivision = true
    assert(failures.exists(_.startsWith("quot(")), failures.mkString("\n"))
  }

  /** The summary of the runs on the functions of `files`, and the runs on which the two semantics
    * differ. */
  private def compare(paths: Seq[String], seed: Int): (String, Seq[String]) = {
    given ctx: inox.Context = stainless.TestContext.empty
    val (_, xlangProgram) = loadFiles(paths)
    val run = verification.VerificationComponent.run(extraction.pipeline)
    val program = inox.Program(run.trees)(run.extract(xlangProgram.symbols)._1)
    val encoder = solvers.InoxEncoder(program, ctx)
    val encoded = encoder.targetProgram

    val sourceFuns = Stainless.functions(using program.symbols)
    val targetFuns = Inox.functions(using encoded.symbols)
    val sourceP = Stainless.program(sourceFuns)(using program.symbols)
    val targetP = Inox.program(targetFuns)(using encoded.symbols)

    // The functions whose callees are all in the fragment, in both programs
    def closed(id: inox.Identifier): Boolean = {
      val callees = program.symbols.transitiveCallees(id) + id
      callees.forall(c => sourceFuns.contains(c) && targetFuns.contains(c))
    }
    val entries = program.symbols.functions.values.toSeq
      .filter(fd => fd.tparams.isEmpty && !fd.flags.exists(_.name == "library") && closed(fd.id))
      .sortBy(_.id.name)

    val rnd = new scala.util.Random(seed)
    val counts = scala.collection.mutable.Map[String, Int]().withDefaultValue(0)
    val failures = scala.collection.mutable.ListBuffer[String]()
    for (fd <- entries) {
      given stainless.trees.Symbols = program.symbols
      import stainless.trees as st
      for (_ <- 0 until inputsPerFunction) {
        val args = fd.params.map(p => value(p.tpe, 3, rnd))
        if (args.forall(_.isDefined)) {
          val call = st.FunctionInvocation(fd.id, Seq(), args.flatten)
          val pre = st.exprOps.preconditionOf(fd.fullBody).getOrElse(st.BooleanLiteral(true))
          val bound = fd.params.zip(args.flatten).foldRight(pre) { case ((p, a), b) => st.Let(p, a, b) }
          val outcome = try {
            val preHolds = Sem.eval(sourceP, fuel, S.Env(S.Nil(), S.Nil()), Stainless.expr(bound).get) == S.Ok(S.BoolV(true))
            if (!preHolds) Outcome.Skipped
            else {
              val src = Sem.eval(sourceP, fuel, S.Env(S.Nil(), S.Nil()), Stainless.expr(call).get)
              if (src == S.Stuck()) Outcome.SourceStuck
              else {
                val tgtCall = encoder.encode(call)
                val tgt = Sem.eval(targetP, fuel, S.Env(S.Nil(), S.Nil()), Inox.expr(tgtCall.asInstanceOf[inox.trees.Expr])(using encoded.symbols).get)
                if (same(src, tgt)) Outcome.Agree
                else Outcome.Differ(s"${fd.id.name}(${args.flatten.mkString(", ")}): Stainless gives $src, Inox gives $tgt")
              }
            }
          } catch {
            case _: Unsupported | _: StackOverflowError => Outcome.Skipped
          }
          outcome match {
            case Outcome.Differ(msg) => failures += msg; counts("differ") += 1
            case o => counts(o.toString) += 1
          }
        }
      }
    }
    (s"${entries.size} functions in the fragment of ${program.symbols.functions.size}; " +
      s"runs: ${counts("Agree")} agree, ${counts("SourceStuck")} where Stainless is stuck, ${counts("Skipped")} skipped, ${counts("differ")} differ",
      failures.toSeq)
  }
}
