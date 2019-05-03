import sbt.ScriptedPlugin

enablePlugins(GitVersioning)
git.baseVersion in ThisBuild := "0.1.0"
git.formattedShaVersion in ThisBuild := git.gitHeadCommit.value map { sha => s"${git.baseVersion.value}-${sha}" }

val osInf = Option(System.getProperty("os.name")).getOrElse("")

val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
val isWindows = osInf.indexOf("Win") >= 0
val isMac     = osInf.indexOf("Mac") >= 0

val osName = if (isWindows) "win" else if (isMac) "mac" else "unix"
val osArch = System.getProperty("sun.arch.data.model")

val inoxVersion = "1.1.0-322-g6cdfa72"
val dottyLibrary = "dotty-compiler_2.12"
val dottyVersion = "0.12.0-RC1-nonbootstrapped"
val circeVersion = "0.10.0-M2"

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

val SupportedScalaVersions = Seq("2.12.8")

lazy val frontendClass = settingKey[String]("The name of the compiler wrapper used to extract stainless trees")

// FIXME @nv: dotty compiler needs the scala-library and dotty-library (and maybe some other
//            dependencies?) so we set them here through stainless' compile-time dependencies.
lazy val extraClasspath = taskKey[String]("Classpath extensions passed directly to the underlying compiler")

lazy val scriptPath = taskKey[String]("Classpath used in the stainless Bash script")

lazy val baseSettings: Seq[Setting[_]] = Seq(
  organization := "ch.epfl.lara",
  licenses := Seq("AGPL-V3" -> url("https://www.gnu.org/licenses/agpl-3.0.html"))
)

lazy val artifactSettings: Seq[Setting[_]] = baseSettings ++ Seq(
  scalaVersion := crossScalaVersions.value.head,
  crossScalaVersions := SupportedScalaVersions
)

lazy val commonSettings: Seq[Setting[_]] = artifactSettings ++ Seq(
  scalacOptions ++= Seq(
    "-deprecation",
    "-unchecked",
    "-feature"
  ),

  unmanagedJars in Runtime += {
    root.base / "unmanaged" / s"scalaz3-$osName-$osArch-${scalaBinaryVersion.value}.jar"
  },

  resolvers ++= Seq(
    Resolver.sonatypeRepo("releases"),
    Resolver.typesafeIvyRepo("releases"),
    Resolver.bintrayRepo("epfl-lara", "maven"),
    "uuverifiers" at "http://logicrunch.it.uu.se:4096/~wv/maven"
  ),

  libraryDependencies ++= Seq(
    "ch.epfl.lara" %% "inox" % inoxVersion,
    "ch.epfl.lara" %% "inox" % inoxVersion % "test" classifier "tests",
    "ch.epfl.lara" %% "cafebabe" % "1.2",
    "org.scalatest" %% "scalatest" % "3.0.1" % "test",
    "io.circe" %% "circe-core" % circeVersion,
    "io.circe" %% "circe-generic" % circeVersion,
    "io.circe" %% "circe-parser" % circeVersion
  ),

  // disable documentation packaging in universal:stage to speedup development
  mappings in (Compile, packageDoc) := Seq(),

  concurrentRestrictions in Global += Tags.limitAll(nParallel),

  sourcesInBase in Compile := false,

  Keys.fork in run := true,

  testOptions in Test := Seq(Tests.Argument("-oDF")),

  testOptions in IntegrationTest := Seq(Tests.Argument("-oDF"))
)

lazy val libraryFiles: Seq[(String, File)] = {
  val libFiles = ((root.base / "frontends" / "library") ** "*.scala").get
  val dropCount = (libFiles.head.getPath indexOfSlice "library") + ("library".size + 1 /* for separator */)
  libFiles.map(file => (file.getPath drop dropCount, file)) // Drop the prefix of the path (i.e. everything before "library")
}

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
  unmanagedSourceDirectories   in Compile         += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "main" / "scala"),
  unmanagedSourceDirectories   in Test            += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "test" / "scala"),
  unmanagedSourceDirectories   in IntegrationTest += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "it" / "scala"),

  // We have to use managed resources here to keep sbt's source watcher happy
  resourceGenerators in Compile += Def.task {
    for ((libPath, libFile) <- libraryFiles) yield {
      val resourceFile = (resourceManaged in Compile).value / libPath
      IO.write(resourceFile, IO.read(libFile))
      resourceFile
    }
  }.taskValue,

  test in assembly := {}, // Skip the test during assembly

  sourceGenerators in Compile += Def.task {
    val main = (sourceManaged in Compile).value / "stainless" / "Main.scala"
    def removeSlashU(in: String): String =
      in.replaceAll("\\\\" + "u", "\\\\\"\"\"+\"\"\"u")
      .replaceAll("\\\\" + "U", "\\\\\"\"\"+\"\"\"U")

    IO.write(main,
      s"""|package stainless
          |
          |object Main extends MainHelpers {
          |
          |  val extraClasspath = "${extraClasspath.value}"
          |  val extraCompilerArguments = List("-classpath", "${extraClasspath.value}")
          |
          |  val libraryPaths = List(
          |    ${removeSlashU(libraryFiles.map(_._1).mkString("\"\"\"", "\"\"\",\n    \"\"\"", "\"\"\""))}
          |  )
          |
          |  override val factory = new frontends.${frontendClass.value}.Factory(extraCompilerArguments, libraryPaths)
          |
          |}""".stripMargin)
    Seq(main)
  }) ++
  inConfig(IntegrationTest)(Defaults.testTasks ++ Seq(
    logBuffered := (nParallel > 1),
    parallelExecution := (nParallel > 1)
  ))

val scriptSettings: Seq[Setting[_]] = Seq(
  extraClasspath := {
    ((classDirectory in Compile).value.getAbsolutePath +: (dependencyClasspath in Compile).value.map(_.data.absolutePath))
      .mkString(System.getProperty("path.separator"))
  }
)


def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

//lazy val inox = RootProject(file("../inox"))
//lazy val dotty = ghProject("git://github.com/lampepfl/dotty.git", "b3194406d8e1a28690faee12257b53f9dcf49506")

// Allow integration test to use facilities from regular tests
lazy val IntegrationTest = config("it") extend(Test)

lazy val `stainless-core` = (project in file("core"))
  .disablePlugins(AssemblyPlugin)
  //.enablePlugins(SphinxPlugin)
  .settings(name := "stainless-core")
  .settings(commonSettings, publishMavenSettings)
  //.settings(site.settings)
  //.dependsOn(inox % "compile->compile;test->test")

lazy val `stainless-library` = (project in file("frontends") / "library")
  .disablePlugins(AssemblyPlugin)
  .settings(commonSettings, publishMavenSettings)
  .settings(
    name := "stainless-library",
    // don't publish binaries - stainless-library is only consumed as a sources component
    publishArtifact in packageBin := false,
    crossVersion := CrossVersion.full,
    scalaSource in Compile := baseDirectory.value
  )

lazy val stainlessBuildInfoKeys = Seq[BuildInfoKey](
  name,
  version,
  scalaVersion,
  sbtVersion
)

lazy val `stainless-scalac` = (project in file("frontends") / "scalac")
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(BuildInfoPlugin)
  .settings(
    name := "stainless-scalac",
    frontendClass := "scalac.ScalaCompiler",
    extraClasspath := "", // no need for the classpath extension with scalac
    libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value,
    buildInfoKeys := stainlessBuildInfoKeys ++ Seq[BuildInfoKey]("useJavaClassPath" -> false),
    buildInfoPackage := "stainless",
    assemblyOption in assembly := (assemblyOption in assembly).value.copy(includeScala = false),
    assemblyExcludedJars in assembly := {
      val cp = (fullClasspath in assembly).value
      // Don't include scalaz3 dependency because it is OS dependent
      cp filter {_.data.getName.startsWith("scalaz3")}
    },
    publish := (()),
    skip in publish := true // following https://github.com/sbt/sbt-assembly#q-despite-the-concerned-friends-i-still-want-publish-fat-jars-what-advice-do-you-have
  )
  .dependsOn(`stainless-core`)
  //.dependsOn(inox % "test->test;it->test,it")
  .configs(IntegrationTest)
  .settings(commonSettings, commonFrontendSettings, scriptSettings)

// Following https://github.com/sbt/sbt-assembly#q-despite-the-concerned-friends-i-still-want-publish-fat-jars-what-advice-do-you-have
lazy val `stainless-scalac-plugin` = (project in file("frontends") / "stainless-scalac-plugin")
  .settings(
    name := "stainless-scalac-plugin",
    crossVersion := CrossVersion.full, // because compiler api is not binary compatible
    packageBin in Compile := (assembly in (`stainless-scalac`, Compile)).value
  )
  .settings(artifactSettings, publishMavenSettings)

lazy val `stainless-scalac-standalone` = (project in file("frontends") / "stainless-scalac-standalone")
  .enablePlugins(BuildInfoPlugin)
  .enablePlugins(JavaAppPackaging)
  .settings(
    name := "stainless-scalac-standalone",
    buildInfoKeys := stainlessBuildInfoKeys ++ Seq[BuildInfoKey]("useJavaClassPath" -> true),
    buildInfoPackage := "stainless",
    (mainClass in assembly) := Some("stainless.Main"),
    (assemblyJarName in assembly) := (name.value + "-" + (git.baseVersion in ThisBuild).value + ".jar"),
    (assemblyMergeStrategy in assembly) := {
      // The BuildInfo class file from the current project comes before the one from `stainless-scalac`,
      // hence the following merge strategy picks the standalone BuildInfo over the usual one.
      case "stainless/BuildInfo$.class" => MergeStrategy.first
      case x =>
        val oldStrategy = (assemblyMergeStrategy in assembly).value
        oldStrategy(x)
    }
  )
  .dependsOn(`stainless-scalac`)
  .settings(artifactSettings)

lazy val `stainless-dotty-frontend` = (project in file("frontends/dotty"))
  .settings(name := "stainless-dotty-frontend")
  .dependsOn(`stainless-core`)
  .settings(libraryDependencies += "ch.epfl.lamp" % dottyLibrary % dottyVersion % "provided")
  .settings(commonSettings)

lazy val `stainless-dotty` = (project in file("frontends/stainless-dotty"))
  .enablePlugins(JavaAppPackaging)
  .settings(
    name := "stainless-dotty",
    frontendClass := "dotc.DottyCompiler")
  //.dependsOn(inox % "test->test;it->test,it")
  .dependsOn(`stainless-dotty-frontend`)
  .aggregate(`stainless-dotty-frontend`)
  // Should truly depend on dotty, overriding the "provided" modifier above:
  .settings(libraryDependencies += "ch.epfl.lamp" % dottyLibrary % dottyVersion)
  .configs(IntegrationTest)
  .settings(commonSettings, commonFrontendSettings, artifactSettings, scriptSettings)

lazy val `sbt-stainless` = (project in file("sbt-plugin"))
  .enablePlugins(BuildInfoPlugin)
  .enablePlugins(SbtPlugin)
  .settings(baseSettings)
  .settings(publishSbtSettings)
  .settings(
    description := "Plugin integrating Stainless in sbt",
    sbtPlugin := true,
    buildInfoUsePackageAsPath := true,
    buildInfoPackage := "ch.epfl.lara.sbt.stainless",
    buildInfoKeys := Seq[BuildInfoKey](
      BuildInfoKey.map(version) { case (_, v) => "stainlessVersion" -> v },
      "supportedScalaVersions" -> SupportedScalaVersions
    )
  )
  .settings(
    scripted := scripted.tag(Tags.Test).evaluated,
    scriptedLaunchOpts ++= Seq(
      "-Xmx768m",
      "-XX:MaxMetaspaceSize=384m",
      "-Dplugin.version=" + version.value,
      "-Dscala.version=" + sys.props.get("scripted.scala.version").getOrElse((scalaVersion in `stainless-scalac`).value)
    ),
    scriptedBufferLog := false,
    scriptedDependencies := {
      publishLocal.value
      (update in `stainless-library`).value
      (publishLocal in `stainless-library`).value
      (publishLocal in `stainless-scalac-plugin`).value
    }
  )

lazy val root = (project in file("."))
  .disablePlugins(AssemblyPlugin)
  .settings(artifactSettings)
  .settings(
    sourcesInBase in Compile := false,
    publishArtifact := false, // Don't publish root project
    publish := (())
  )
  .dependsOn(`stainless-scalac`, `stainless-library`, `stainless-dotty`, `sbt-stainless`)
  .aggregate(`stainless-core`, `stainless-library`, `stainless-scalac`, `stainless-dotty`, `sbt-stainless`, `stainless-scalac-plugin`)

def commonPublishSettings = Seq(
  bintrayOrganization := Some("epfl-lara")
)

// by default sbt-bintray publishes all sbt plugins in Ivy style
def publishSbtSettings = commonPublishSettings ++ Seq(
  bintrayRepository := "sbt-plugins"
)

// by default sbt-bintray publishes all artifacts but sbt plugins in Maven style
def publishMavenSettings = commonPublishSettings ++ Seq(
  bintrayRepository := "maven"
)

// FIXME assembly should be disabled at the top level, but isn't
// FIXME assembly is not compatible with dotty -- some conflict with scala versions?

