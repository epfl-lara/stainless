
val osInf = Option(System.getProperty("os.name")).getOrElse("")

val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
val isWindows = osInf.indexOf("Win") >= 0
val isMac     = osInf.indexOf("Mac") >= 0

val osName = if (isWindows) "win" else if (isMac) "mac" else "unix"
val osArch = System.getProperty("sun.arch.data.model")

val inoxVersion = "1.0.2-130-g3775bf8"
val dottyVersion = "0.1.1-bin-20170429-10a2ce6-NIGHTLY"

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

// FIXME @nv: dotty compiler needs the scala-library and dotty-library (and maybe some other
//            dependencies?) so we set them here through stainless' compile-time dependencies.
lazy val extraClasspath = taskKey[String]("Classpath extensions passed directly to the underlying compiler")

lazy val scriptPath = taskKey[String]("Classpath used in the stainless Bash script")

lazy val script = taskKey[Unit]("Generate the stainless Bash script")

lazy val scalaVersionSetting: Setting[_] = scalaVersion := "2.11.8"

lazy val artifactSettings: Seq[Setting[_]] = Seq(
  version := "0.1",
  organization := "ch.epfl.lara",
  scalaVersionSetting
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
    "uuverifiers" at "http://logicrunch.it.uu.se:4096/~wv/maven",
    Resolver.typesafeIvyRepo("releases")
  ),

  libraryDependencies ++= Seq(
    "ch.epfl.lara" %% "inox" % inoxVersion,
    "ch.epfl.lara" %% "inox" % inoxVersion % "test" classifier "tests",
    "org.scalatest" %% "scalatest" % "3.0.1" % "test",
    "org.json4s" %% "json4s-native" % "3.5.2"
  ),

  concurrentRestrictions in Global += Tags.limit(Tags.Test, nParallel),

  sourcesInBase in Compile := false,

  Keys.fork in run := true,

  testOptions in Test := Seq(Tests.Argument("-oDF")),

  testOptions in IntegrationTest := Seq(Tests.Argument("-oDF"))
)

lazy val commonFrontendSettings: Seq[Setting[_]] = Defaults.itSettings ++ Seq(
  libraryDependencies ++= Seq(
    "ch.epfl.lara" %% "inox" % inoxVersion % "it" classifier "tests" classifier "it",
    "org.scalatest" %% "scalatest" % "3.0.1" % "it" // FIXME: Does this override `% "test"` from commonSettings above?
  ),

  /**
    * NOTE: IntelliJ seems to have trouble including sources located outside the base directory of an
    *   sbt project. You can temporarily disable the following four lines when importing the project.
    */
  unmanagedResourceDirectories in IntegrationTest += (root.base / "frontends" / "benchmarks"),
  unmanagedSourceDirectories in Compile += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "main" / "scala"),
  unmanagedSourceDirectories in Test += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "test" / "scala"),
  unmanagedSourceDirectories in IntegrationTest += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "it" / "scala"),

  sourceGenerators in Compile <+= Def.task {
    val libraryFiles = ((root.base / "frontends" / "library") ** "*.scala").getPaths
    val main = (sourceManaged in Compile).value / "stainless" / "Main.scala"
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
                       |  ) = frontends.${frontendClass.value}(ctx, List("-classpath", "${extraClasspath.value}") ++ compilerOpts)
                       |}""".stripMargin)
    Seq(main)
  }) ++
  inConfig(IntegrationTest)(Defaults.testTasks ++ Seq(
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

  scriptPath := {
    val cps = (managedClasspath in Runtime).value ++
      (unmanagedClasspath in Runtime).value ++
      (internalDependencyClasspath in Runtime).value

    val out = (classDirectory      in Compile).value
    val res = (resourceDirectory   in Compile).value

    (res.getAbsolutePath +: out.getAbsolutePath +: cps.map(_.data.absolutePath)).mkString(System.getProperty("path.separator"))
  },

  extraClasspath := {
    ((classDirectory in Compile).value.getAbsolutePath +: (dependencyClasspath in Compile).value.map(_.data.absolutePath))
      .mkString(System.getProperty("path.separator"))
  },

  script := {
    val s = streams.value
    try {
      val binDir = root.base / "bin"
      binDir.mkdirs

      val scriptFile = binDir / name.value

      if (scriptFile.exists) {
        s.log.info("Regenerating '" + scriptFile.getName + "' script")
        scriptFile.delete
      } else {
        s.log.info("Generating '" + scriptFile.getName + "' script")
      }

      val paths = scriptPath.value
      IO.write(scriptFile, s"""|#!/bin/bash --posix
                               |
                               |set -o pipefail
                               |
                               |SCALACLASSPATH="$paths"
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
//lazy val dotty = ghProject("git://github.com/lampepfl/dotty.git", "b3194406d8e1a28690faee12257b53f9dcf49506")
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
    extraClasspath := "", // no need for the classpath extension with scalac
    libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value)
  .dependsOn(`stainless-core`)
  //.dependsOn(inox % "test->test;it->test,it")
  .configs(IntegrationTest)
  .settings(commonSettings, commonFrontendSettings, scriptSettings)

lazy val `stainless-dotty-frontend` = (project in file("frontends/dotty"))
  .settings(name := "stainless-dotty-frontend")
  .dependsOn(`stainless-core`)
  .settings(libraryDependencies += "ch.epfl.lamp" % "dotty_2.11" % dottyVersion % "provided")
  .settings(commonSettings)

lazy val `stainless-dotty` = (project in file("frontends/stainless-dotty"))
  .settings(
    name := "stainless-dotty",
    frontendClass := "dotc.DottyCompiler")
  .dependsOn(`stainless-dotty-frontend`)
  // Should truly depend on dotty, overriding the "provided" modifier above:
  .settings(libraryDependencies += "ch.epfl.lamp" % "dotty_2.11" % dottyVersion)
  .aggregate(`stainless-dotty-frontend`)
  //.dependsOn(inox % "test->test;it->test,it")
  .configs(IntegrationTest)
  .settings(commonSettings, commonFrontendSettings, artifactSettings, scriptSettings)

lazy val root = (project in file("."))
  .settings(scalaVersionSetting, sourcesInBase in Compile := false)
  .dependsOn(`stainless-scalac`, `stainless-dotty`)
  .aggregate(`stainless-core`, `stainless-scalac`, `stainless-dotty`)
