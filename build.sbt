val osName = if (Option(System.getProperty("os.name")).getOrElse("").toLowerCase contains "win") "win" else "unix"
val osArch = System.getProperty("sun.arch.data.model")

val inoxVersion = "1.0.2-2-gb5fdc3d"

lazy val nParallel = {
  val p = System.getProperty("parallel")
  if (p ne null) {
    try {
      p.toInt
    } catch {
      case nfe: NumberFormatException => 1
    }
  } else {
    1
  }
}

lazy val frontendClass = settingKey[String]("The name of the compiler wrapper used to extract stainless trees")

lazy val script = taskKey[Unit]("Generate the stainless Bash script")

lazy val artifactSettings: Seq[Setting[_]] = Seq(
  version := "0.1",
  organization := "ch.epfl.lara",
  scalaVersion := "2.11.8"
)

lazy val commonSettings: Seq[Setting[_]] = artifactSettings ++ Seq(
  scalacOptions ++= Seq(
    "-deprecation",
    "-unchecked",
    "-feature"
  ),

  scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", baseDirectory.value+"/src/main/scala/root-doc.txt"),

  // TODO: Reenable site.settings
//  site.settings,
//  site.sphinxSupport(),

  unmanagedJars in Runtime += {
    root.base / "unmanaged" / s"scalaz3-$osName-$osArch-${scalaBinaryVersion.value}.jar"
  },

  resolvers ++= Seq(
    "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
    "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases",
    "uuverifiers" at "http://logicrunch.it.uu.se:4096/~wv/maven"
  ),

  libraryDependencies ++= Seq(
    //"ch.epfl.lamp" %% "dotty" % "0.1-SNAPSHOT",
    "ch.epfl.lara" %% "inox" % inoxVersion,
    "ch.epfl.lara" %% "inox" % inoxVersion % "test" classifier "tests",
    "org.scalatest" %% "scalatest" % "3.0.1" % "test"
  ),

  concurrentRestrictions in Global += Tags.limit(Tags.Test, nParallel),

  sourcesInBase in Compile := false,

  Keys.fork in run := true,

  testOptions in Test := Seq(Tests.Argument("-oDF")),

  testOptions in IntegrationTest := Seq(Tests.Argument("-oDF"))
)

lazy val commonFrontendSettings: Seq[Setting[_]] = Seq(
  libraryDependencies ++= Seq(
    "ch.epfl.lara" %% "inox" % inoxVersion % "it" classifier "tests" classifier "it",
    "org.scalatest" %% "scalatest" % "3.0.1" % "it"  // FIXME: Does this override `% "test"` from commonSettings above?
  ),

  sourceGenerators in Compile <+= Def.task {
    val libraryFiles = ((root.base / "frontends" / "library") ** "*.scala").getPaths
    val main = (sourceManaged in Compile).value / "stainless" / "Main.scala"
    val extractFromSourceSig = """def extractFromSource(ctx: inox.Context, compilerOpts: List[String]): (
                                 |    List[xt.UnitDef],
                                 |    Program { val trees: xt.type }
                                 |  )""".stripMargin
    IO.write(main, s"""|package stainless
                       |
                       |import extraction.xlang.{trees => xt}
                       |
                       |object Main extends MainHelpers {
                       |  val libraryFiles = List(
                          ${libraryFiles
      .mkString("\"\"\"", "\"\"\",\n    \"\"\"", "\"\"\"")
      .replaceAll("\\\\" + "u", "\\\\\"\"\"+\"\"\"u")}
                       |  )
                       |
                       |  def extractFromSource(ctx: inox.Context, compilerOpts: List[String]): (
                       |    List[xt.UnitDef],
                       |    Program { val trees: xt.type }
                       |  ) = frontends.${frontendClass.value}(ctx, compilerOpts)
                       |}""".stripMargin)
    Seq(main)
  }
) ++ Defaults.itSettings ++ inConfig(IntegrationTest)(Defaults.testTasks ++ Seq(
  logBuffered := (nParallel > 1),
  parallelExecution := (nParallel > 1)
))

val scriptSettings: Seq[Setting[_]] = Seq(
  compile <<= (compile in Compile) dependsOn script,

  clean := {
    clean.value
    val scriptFile = root.base / "bin" / name.value
    if (scriptFile.exists && scriptFile.isFile) {
      scriptFile.delete
    }
  },

  script := {
    val s = streams.value
    try {
      val binDir = root.base / "bin"
      binDir.mkdirs

      val scriptFile = binDir / name.value

      val cps = (managedClasspath in Runtime).value ++
        (unmanagedClasspath in Runtime).value ++
        (internalDependencyClasspath in Runtime).value

      val out = (classDirectory      in Compile).value
      val res = (resourceDirectory   in Compile).value

      if (scriptFile.exists) {
        s.log.info("Regenerating '" + scriptFile.getName + "' script")
        scriptFile.delete
      } else {
        s.log.info("Generating '" + scriptFile.getName + "' script")
      }

      val paths = (res.getAbsolutePath +: out.getAbsolutePath +: cps.map(_.data.absolutePath)).mkString(System.getProperty("path.separator"))
      IO.write(scriptFile, s"""|#!/bin/bash --posix
                               |
                               |SCALACLASSPATH=$paths
                               |
                               |java -Xmx2G -Xms512M -Xss64M -classpath "$${SCALACLASSPATH}" -Dscala.usejavacp=true stainless.Main $$@ 2>&1 | tee -i last.log
                               |""".stripMargin)
      scriptFile.setExecutable(true)
    } catch {
      case e: Throwable =>
        s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
    }
  }
)


def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

//lazy val inox = RootProject(file("../inox"))
lazy val dotty = ghProject("git://github.com/lampepfl/dotty.git", "fb1dbba5e35d1fc7c00250f597b8c796d8c96eda")
lazy val cafebabe = ghProject("git://github.com/psuter/cafebabe.git", "49dce3c83450f5fa0b5e6151a537cc4b9f6a79a6")


lazy val `stainless-core` = (project in file("core"))
  .settings(name := "stainless-core")
  .settings(commonSettings)
  //.dependsOn(inox % "compile->compile;test->test")
  .dependsOn(cafebabe)

lazy val `stainless-scalac` = (project in file("frontends/scalac"))
  .settings(
    name := "stainless-scalac",
    frontendClass := "scalac.ScalaCompiler",
    libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value)
  .dependsOn(`stainless-core`)
  //.dependsOn(inox % "test->test;it->test,it")
  .configs(IntegrationTest)
  .settings(commonSettings, commonFrontendSettings, scriptSettings)

lazy val `stainless-dotty-frontend` = (project in file("frontends/dotty"))
  .settings(name := "stainless-dotty-frontend")
  .dependsOn(`stainless-core`, dotty % "provided")
  .settings(commonSettings)

lazy val `stainless-dotty` = (project in file("frontends/stainless-dotty"))
  .settings(
    name := "stainless-dotty",
    frontendClass := "dotc.DottyCompiler",
    /** 
      * NOTE: IntelliJ seems to have trouble including sources located outside the base directory of an
      *   sbt project. You can temporarily disable the following two lines when importing the project.
      */
    unmanagedResourceDirectories in IntegrationTest += file(".") / "frontends" / "scalac" / "it" / "resources")
  .dependsOn(`stainless-dotty-frontend`, dotty)  // Should truly depend on dotty, overriding the "provided" modifier above
  .aggregate(`stainless-dotty-frontend`)
  .configs(IntegrationTest)
  .settings(commonSettings, commonFrontendSettings, artifactSettings, scriptSettings)

lazy val root = (project in file("."))
  .settings(sourcesInBase in Compile := false)
  .dependsOn(`stainless-scalac`, `stainless-dotty`)
  .aggregate(`stainless-core`, `stainless-scalac`, `stainless-dotty`)
