package stainless.frontends.fast

import stainless.MainHelpers

object Main extends MainHelpers {

  val extraClasspath = "/home/stevan/Documents/semester_project/stainless/frontends/fast/target/scala-2.11/classes:/home/stevan/Documents/semester_project/stainless/frontends/dotty/target/scala-2.11/classes:/home/stevan/Documents/semester_project/stainless/core/target/scala-2.11/classes:/home/stevan/Documents/semester_project/inox/target/scala-2.11/classes:/home/stevan/Documents/semester_project/inox/unmanaged/scalaz3-unix-64-2.11.jar:/home/stevan/.ivy2/cache/org.scala-lang/scala-library/jars/scala-library-2.11.8.jar:/home/stevan/.ivy2/cache/org.apache.commons/commons-lang3/jars/commons-lang3-3.4.jar:/home/stevan/.ivy2/cache/org.scala-lang/scala-reflect/jars/scala-reflect-2.11.8.jar:/home/stevan/.ivy2/cache/com.regblanc/scala-smtlib_2.11/jars/scala-smtlib_2.11-0.2.2-7-g00a9686.jar:/home/stevan/.ivy2/cache/uuverifiers/princess_2.11/jars/princess_2.11-2018-02-26.jar:/home/stevan/.ivy2/cache/uuverifiers/princess-parser_2.11/jars/princess-parser_2.11-2018-02-26.jar:/home/stevan/.ivy2/cache/uuverifiers/princess-smt-parser_2.11/jars/princess-smt-parser_2.11-2018-02-26.jar:/home/stevan/.ivy2/cache/org.scala-lang.modules/scala-parser-combinators_2.11/bundles/scala-parser-combinators_2.11-1.0.4.jar:/home/stevan/.ivy2/cache/net.sf.squirrel-sql.thirdparty-non-maven/java-cup/jars/java-cup-0.11a.jar:/home/stevan/.ivy2/cache/ch.epfl.lara/cafebabe_2.11/jars/cafebabe_2.11-1.2.jar:/home/stevan/.ivy2/cache/io.circe/circe-core_2.11/jars/circe-core_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/io.circe/circe-numbers_2.11/jars/circe-numbers_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/org.typelevel/cats-core_2.11/jars/cats-core_2.11-1.2.0.jar:/home/stevan/.ivy2/cache/org.typelevel/cats-macros_2.11/jars/cats-macros_2.11-1.2.0.jar:/home/stevan/.ivy2/cache/org.typelevel/machinist_2.11/jars/machinist_2.11-0.6.4.jar:/home/stevan/.ivy2/cache/org.typelevel/cats-kernel_2.11/jars/cats-kernel_2.11-1.2.0.jar:/home/stevan/.ivy2/cache/io.circe/circe-generic_2.11/jars/circe-generic_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/com.chuusai/shapeless_2.11/bundles/shapeless_2.11-2.3.3.jar:/home/stevan/.ivy2/cache/org.typelevel/macro-compat_2.11/jars/macro-compat_2.11-1.1.1.jar:/home/stevan/.ivy2/cache/io.circe/circe-parser_2.11/jars/circe-parser_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/io.circe/circe-jawn_2.11/jars/circe-jawn_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/org.spire-math/jawn-parser_2.11/jars/jawn-parser_2.11-0.13.0.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty_2.11/jars/dotty_2.11-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty-compiler_2.11/jars/dotty-compiler_2.11-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty-interfaces/jars/dotty-interfaces-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty-library_2.11/jars/dotty-library_2.11-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/org.scala-lang.modules/scala-asm/bundles/scala-asm-5.1.0-scala-2.jar:/home/stevan/.ivy2/cache/org.scala-sbt/interface/jars/interface-0.13.15.jar:/home/stevan/.ivy2/cache/org.scala-lang.modules/scala-xml_2.11/bundles/scala-xml_2.11-1.0.1.jar"
  val extraCompilerArguments = List("-classpath", "/home/stevan/Documents/semester_project/stainless/frontends/fast/target/scala-2.11/classes:/home/stevan/Documents/semester_project/stainless/frontends/dotty/target/scala-2.11/classes:/home/stevan/Documents/semester_project/stainless/core/target/scala-2.11/classes:/home/stevan/Documents/semester_project/inox/target/scala-2.11/classes:/home/stevan/Documents/semester_project/inox/unmanaged/scalaz3-unix-64-2.11.jar:/home/stevan/.ivy2/cache/org.scala-lang/scala-library/jars/scala-library-2.11.8.jar:/home/stevan/.ivy2/cache/org.apache.commons/commons-lang3/jars/commons-lang3-3.4.jar:/home/stevan/.ivy2/cache/org.scala-lang/scala-reflect/jars/scala-reflect-2.11.8.jar:/home/stevan/.ivy2/cache/com.regblanc/scala-smtlib_2.11/jars/scala-smtlib_2.11-0.2.2-7-g00a9686.jar:/home/stevan/.ivy2/cache/uuverifiers/princess_2.11/jars/princess_2.11-2018-02-26.jar:/home/stevan/.ivy2/cache/uuverifiers/princess-parser_2.11/jars/princess-parser_2.11-2018-02-26.jar:/home/stevan/.ivy2/cache/uuverifiers/princess-smt-parser_2.11/jars/princess-smt-parser_2.11-2018-02-26.jar:/home/stevan/.ivy2/cache/org.scala-lang.modules/scala-parser-combinators_2.11/bundles/scala-parser-combinators_2.11-1.0.4.jar:/home/stevan/.ivy2/cache/net.sf.squirrel-sql.thirdparty-non-maven/java-cup/jars/java-cup-0.11a.jar:/home/stevan/.ivy2/cache/ch.epfl.lara/cafebabe_2.11/jars/cafebabe_2.11-1.2.jar:/home/stevan/.ivy2/cache/io.circe/circe-core_2.11/jars/circe-core_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/io.circe/circe-numbers_2.11/jars/circe-numbers_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/org.typelevel/cats-core_2.11/jars/cats-core_2.11-1.2.0.jar:/home/stevan/.ivy2/cache/org.typelevel/cats-macros_2.11/jars/cats-macros_2.11-1.2.0.jar:/home/stevan/.ivy2/cache/org.typelevel/machinist_2.11/jars/machinist_2.11-0.6.4.jar:/home/stevan/.ivy2/cache/org.typelevel/cats-kernel_2.11/jars/cats-kernel_2.11-1.2.0.jar:/home/stevan/.ivy2/cache/io.circe/circe-generic_2.11/jars/circe-generic_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/com.chuusai/shapeless_2.11/bundles/shapeless_2.11-2.3.3.jar:/home/stevan/.ivy2/cache/org.typelevel/macro-compat_2.11/jars/macro-compat_2.11-1.1.1.jar:/home/stevan/.ivy2/cache/io.circe/circe-parser_2.11/jars/circe-parser_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/io.circe/circe-jawn_2.11/jars/circe-jawn_2.11-0.10.0-M2.jar:/home/stevan/.ivy2/cache/org.spire-math/jawn-parser_2.11/jars/jawn-parser_2.11-0.13.0.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty_2.11/jars/dotty_2.11-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty-compiler_2.11/jars/dotty-compiler_2.11-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty-interfaces/jars/dotty-interfaces-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/ch.epfl.lamp/dotty-library_2.11/jars/dotty-library_2.11-0.1.1-bin-20170429-10a2ce6-NIGHTLY.jar:/home/stevan/.ivy2/cache/org.scala-lang.modules/scala-asm/bundles/scala-asm-5.1.0-scala-2.jar:/home/stevan/.ivy2/cache/org.scala-sbt/interface/jars/interface-0.13.15.jar:/home/stevan/.ivy2/cache/org.scala-lang.modules/scala-xml_2.11/bundles/scala-xml_2.11-1.0.1.jar")

  val libraryPaths = List(
    """stainless/annotation.scala""",
    """stainless/proof/package.scala""",
    """stainless/proof/Internal.scala""",
    """stainless/equations/package.scala""",
    """stainless/collection/List.scala""",
    """stainless/util/Random.scala""",
    """stainless/lang/Rational.scala""",
    """stainless/lang/StrOps.scala""",
    """stainless/lang/package.scala""",
    """stainless/lang/Either.scala""",
    """stainless/lang/Map.scala""",
    """stainless/lang/Option.scala""",
    """stainless/lang/Set.scala""",
    """stainless/lang/Bag.scala""",
    """stainless/lang/Real.scala""",
    """stainless/lang/PartialFunction.scala""",
    """stainless/lang/StaticChecks.scala""",
    """stainless/io/package.scala""",
    """stainless/io/FileInputStream.scala""",
    """stainless/io/StdIn.scala""",
    """stainless/io/FileOutputStream.scala""",
    """stainless/io/StdOut.scala""",
    """stainless/math/package.scala""",
    """stainless/annotation/isabelle.scala"""
  )

  override val factory = new FastCompiler.Factory(extraCompilerArguments, Seq())

}