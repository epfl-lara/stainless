import sbt.ScriptedPlugin

enablePlugins(GitVersioning)
enablePlugins(GitBranchPrompt)

git.useGitDescribe := true

Global / excludeLintKeys += buildInfoKeys
Global / excludeLintKeys += buildInfoOptions
Global / excludeLintKeys += buildInfoPackage
Global / excludeLintKeys += testOptions
Global / excludeLintKeys += publishArtifact

val osInf = Option(System.getProperty("os.name")).getOrElse("")

val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
val isWindows = osInf.indexOf("Win") >= 0
val isMac     = osInf.indexOf("Mac") >= 0

val osName = if (isWindows) "win" else if (isMac) "mac" else "unix"
val osArch = System.getProperty("sun.arch.data.model")

val dottyLibrary = "dotty-compiler_2.12"
val dottyVersion = "0.12.0-RC1-nonbootstrapped"
val circeVersion = "0.14.1"

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

// Stainless itself uses Scala 3...
val stainlessScalaVersion = "3.0.2"
// ...whereas Stainless programs use Scala 2.13
val stainlessProgScalaVersion = "2.13.6"

scalaVersion := stainlessScalaVersion

lazy val frontendClass = settingKey[String]("The name of the compiler wrapper used to extract stainless trees")

// FIXME @nv: dotty compiler needs the scala-library and dotty-library (and maybe some other
//            dependencies?) so we set them here through stainless' compile-time dependencies.
lazy val extraClasspath = taskKey[String]("Classpath extensions passed directly to the underlying compiler")

lazy val scriptPath = taskKey[String]("Classpath used in the stainless Bash script")

lazy val stainlessBuildInfoKeys = Seq[BuildInfoKey](
  name,
  version,
  scalaVersion,
  sbtVersion,
)

lazy val noPublishSettings: Seq[Setting[_]] = Seq(
  publish         := {},
  publishM2       := {},
  publish / skip := true,
)

lazy val baseSettings: Seq[Setting[_]] = Seq(
  organization := "ch.epfl.lara",
  licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))
)

lazy val artifactSettings: Seq[Setting[_]] = baseSettings ++ Seq(
  scalaVersion := stainlessScalaVersion,

  buildInfoPackage := "stainless",
  buildInfoKeys := stainlessBuildInfoKeys,
  buildInfoOptions := Seq(BuildInfoOption.BuildTime),
)

lazy val commonSettings: Seq[Setting[_]] = artifactSettings ++ Seq(
  scalacOptions ++= Seq(
    "-deprecation",
    "-unchecked",
    "-feature"
  ),

  resolvers ++= Seq(
    Resolver.sonatypeRepo("releases").withAllowInsecureProtocol(true),
    ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven").withAllowInsecureProtocol(true),
  ),

  libraryDependencies ++= Seq(
    // "ch.epfl.lara"    %% "inox"          % inoxVersion,
    // "ch.epfl.lara"    %% "inox"          % inoxVersion % "test" classifier "tests",
    "org.scala-lang.modules" %% "scala-parallel-collections" % "1.0.3",
    "io.circe"               %% "circe-core"                 % circeVersion,
    "io.circe"               %% "circe-generic"              % circeVersion,
    "io.circe"               %% "circe-parser"               % circeVersion,
    ("io.get-coursier"       %% "coursier"                   % "2.0.16").cross(CrossVersion.for3Use2_13),
    "com.typesafe"            % "config"                     % "1.3.4",

    "org.scalatest"   %% "scalatest"     % "3.2.9" % "test"
  ),

  // There is a conflict with the cross version of scala-xml.
  // Coursier depends on 2.13 while scalatest on 3.0.
  // We can get away by excluding 3.0 and using the 2.13 version instead.
  // Note that we leverage excludeDependencies that also excludes the dependency brought by the dependsOn inox.
  excludeDependencies ++= Seq(
    ExclusionRule("org.scala-lang.modules", "scala-xml_3")
  ),

  // disable documentation packaging in universal:stage to speedup development
  Compile / packageDoc / mappings := Seq(),

  Global / concurrentRestrictions += Tags.limitAll(nParallel),

  Compile / sourcesInBase := false,

  run / Keys.fork := true,

  run / javaOptions ++= Seq(
    "-Xss256M",
    "-Xms1024M",
    "-XX:MaxMetaspaceSize=1G",
    "-XX:+UseCodeCacheFlushing",
    "-XX:ReservedCodeCacheSize=256M",
  ),

  /* run / javaOptions += "-agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=5005", */

  Test / testOptions := Seq(Tests.Argument("-oDF")),

  IntegrationTest / testOptions := Seq(Tests.Argument("-oDF")),
)

lazy val stainlessLibSettings: Seq[Setting[_]] = artifactSettings ++ Seq(
  scalacOptions ++= Seq(
    "-deprecation",
    "-unchecked",
    "-feature"
  ),

  // disable documentation packaging in universal:stage to speedup development
  Compile / packageDoc / mappings := Seq(),

  Global / concurrentRestrictions += Tags.limitAll(nParallel),

  Compile / sourcesInBase := false,

  run / Keys.fork := true,

  run / javaOptions ++= Seq(
    "-Xss256M",
    "-Xms1024M",
    "-XX:+UseCodeCacheFlushing",
    "-XX:ReservedCodeCacheSize=256M",
  ),

  /* run / javaOptions += "-agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=5005", */

  Test / testOptions := Seq(Tests.Argument("-oDF")),

  IntegrationTest / testOptions := Seq(Tests.Argument("-oDF"))
)

lazy val assemblySettings: Seq[Setting[_]] = {
  def isNativeLib(file: String): Boolean =
    file.endsWith("dll") || file.endsWith("so") || file.endsWith("jnilib")

  Seq(
    assembly / assemblyMergeStrategy := {
      // The BuildInfo class file from the current project comes after the one from `stainless-scalac`,
      // hence the following merge strategy picks the standalone BuildInfo over the usual one.
      case "stainless/BuildInfo.class" => MergeStrategy.last
      case "stainless/BuildInfo$.class" => MergeStrategy.last
      case PathList("META-INF", xs @ _*) => MergeStrategy.discard
      case PathList("scala", "collection", "compat", _*) => MergeStrategy.first
      case PathList("scala", "annotation", _*) => MergeStrategy.first
      case PathList("scala", "util", _*) => MergeStrategy.first
      case PathList("stainless", _*) => MergeStrategy.first
      case path if path.endsWith("scala-collection-compat.properties") => MergeStrategy.first
      case "reflect.properties" => MergeStrategy.first
      case file if isNativeLib(file) => MergeStrategy.first
      case x =>
        val oldStrategy = (assembly / assemblyMergeStrategy).value
        oldStrategy(x)
    },
  )
}

lazy val libFilesFile = "libfiles.txt" // file storing list of library file names

lazy val regenFilesFile = false

lazy val libraryFiles: Seq[(String, File)] = {
  val libFiles = ((root.base / "frontends" / "library" / "stainless") ** "*.scala").get
  val dropCount = (libFiles.head.getPath indexOfSlice "library") + ("library".size + 1 /* for separator */)
  val res : Seq[(String, File)] = libFiles.map(file => (file.getPath drop dropCount, file)) // Drop the prefix of the path (i.e. everything before "library")
  if (regenFilesFile) {
    val fileNames : Seq[String] = res.map(_._1)
    println(fileNames)
    reflect.io.File(libFilesFile).writeAll(fileNames.mkString("\n"))
  }
  res
}

lazy val commonFrontendSettings: Seq[Setting[_]] = Defaults.itSettings ++ Seq(

  /**
    * NOTE: IntelliJ seems to have trouble including sources located outside the base directory of an
    *   sbt project. You can temporarily disable the following four lines when importing the project.
    */
  IntegrationTest / unmanagedResourceDirectories += (root.base / "frontends" / "benchmarks"),
  Compile / unmanagedSourceDirectories           += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "main" / "scala"),
  Test / unmanagedSourceDirectories              += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "test" / "scala"),
  IntegrationTest / unmanagedSourceDirectories   += (root.base.getAbsoluteFile / "frontends" / "common" / "src" / "it" / "scala"),

  // We have to use managed resources here to keep sbt's source watcher happy
  Compile / resourceGenerators += Def.task {
    for ((libPath, libFile) <- libraryFiles) yield {
      val resourceFile = (Compile / resourceManaged).value / libPath
      IO.write(resourceFile, IO.read(libFile))
      resourceFile
    }
  }.taskValue,

  assembly / test := {}, // Skip the test during assembly

  Compile / sourceGenerators += Def.task {
    val main = (Compile / sourceManaged).value / "stainless" / "Main.scala"
    def removeSlashU(in: String): String =
      in.replaceAll("\\\\" + "u", "\\\\\"\"\"+\"\"\"u")
      .replaceAll("\\\\" + "U", "\\\\\"\"\"+\"\"\"U")

    IO.write(main,
      s"""|package stainless
          |
          |object Main extends MainHelpers {
          |  val defaultPaths = List(${removeSlashU(libraryFiles.map(_._1).mkString("\"\"\"", "\"\"\",\n \"\"\"", "\"\"\""))})
          |  val libPaths = try {
          |    val source = scala.io.Source.fromFile(\"${libFilesFile}\")
          |    try source.getLines().toList finally source.close()
          |  } catch {
          |     case (_:Throwable) => defaultPaths
          |  }
          |
          |  override val factory = new frontends.${frontendClass.value}.Factory(Nil, libPaths)
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
    ((Compile / classDirectory).value.getAbsolutePath +: (Compile / dependencyClasspath).value.map(_.data.absolutePath))
      .mkString(System.getProperty("path.separator"))
  }
)


def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

// lazy val inox = RootProject(file("../inox"))
lazy val inox = ghProject("https://github.com/epfl-lara/inox.git", "993121e9fcb661014855c1a18eba7e6413b35bcd")
lazy val cafebabe = ghProject("https://github.com/epfl-lara/cafebabe.git", "616e639b34379e12b8ac202849de3ebbbd0848bc")
//lazy val dotty = ghProject("git://github.com/lampepfl/dotty.git", "b3194406d8e1a28690faee12257b53f9dcf49506")

// Allow integration test to use facilities from regular tests
lazy val IntegrationTest = config("it") extend(Test)

lazy val `stainless-core` = (project in file("core"))
  .disablePlugins(AssemblyPlugin)
  .enablePlugins(BuildInfoPlugin)
  //.enablePlugins(SphinxPlugin)
  .settings(name := "stainless-core")
  .settings(commonSettings, publishMavenSettings)
  //.settings(site.settings)
  .dependsOn(inox % "compile->compile;test->test")
  .dependsOn(cafebabe % "compile->compile")

lazy val `stainless-library` = (project in file("frontends") / "library")
  .disablePlugins(AssemblyPlugin)
  .settings(stainlessLibSettings, publishMavenSettings)
  .settings(
    name := "stainless-library",
    scalaVersion := stainlessProgScalaVersion,
    // don't publish binaries - stainless-library is only consumed as a sources component
    packageBin / publishArtifact := false,
    crossVersion := CrossVersion.binary,
    Compile / scalaSource := baseDirectory.value / "stainless"
  )

lazy val `stainless-algebra` = (project in file("frontends") / "algebra")
  .disablePlugins(AssemblyPlugin)
  .settings(stainlessLibSettings, publishMavenSettings)
  .settings(
    name := "stainless-algebra",
    version := "0.1.2",
    scalaVersion := stainlessProgScalaVersion,

    // don't publish binaries - stainless-algebra is only consumed as a sources component
    packageBin / publishArtifact := false,
    crossVersion := CrossVersion.binary,
    Compile / scalaSource := baseDirectory.value / "stainless"
  )
  .dependsOn(`stainless-library`)

lazy val `stainless-scalac` = (project in file("frontends") / "scalac")
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(BuildInfoPlugin)
  .settings(commonSettings, commonFrontendSettings)
  .settings(scriptSettings, assemblySettings)
  .settings(noPublishSettings)
  .settings(
    name := "stainless-scalac",
    frontendClass := "scalac.ScalaCompiler",
    libraryDependencies += "org.scala-lang" % "scala-compiler" % stainlessProgScalaVersion,
    buildInfoKeys ++= Seq[BuildInfoKey]("useJavaClassPath" -> false),
    assemblyPackageScala / assembleArtifact := true,
    assembly / assemblyExcludedJars := {
      val cp = (assembly / fullClasspath).value
      // Don't include scalaz3 dependency because it is OS dependent
      cp filter {_.data.getName.startsWith("scalaz3")}
    },
  )
  .dependsOn(`stainless-core`)
  .dependsOn(inox % "test->test;it->test,it")
  .configs(IntegrationTest)

// Following https://github.com/sbt/sbt-assembly#q-despite-the-concerned-friends-i-still-want-publish-fat-jars-what-advice-do-you-have
lazy val `stainless-scalac-plugin` = (project in file("frontends") / "stainless-scalac-plugin")
  .settings(artifactSettings, publishMavenSettings, assemblySettings)
  .settings(
    name := "stainless-scalac-plugin",
    crossVersion := CrossVersion.full, // because compiler api is not binary compatible
    Compile / packageBin := (`stainless-scalac` / Compile / assembly).value
  )

lazy val `stainless-scalac-standalone` = (project in file("frontends") / "stainless-scalac-standalone")
  .enablePlugins(BuildInfoPlugin)
  .enablePlugins(JavaAppPackaging)
  .settings(artifactSettings, assemblySettings)
  .settings(
    name := "stainless-scalac-standalone",
    buildInfoKeys ++= Seq[BuildInfoKey]("useJavaClassPath" -> true),
    assembly / mainClass := Some("stainless.Main"),
    assembly / assemblyJarName := (name.value + "-" + version.value + ".jar"),
    Runtime / unmanagedJars := (`stainless-scalac` / Runtime / unmanagedJars).value
  )
  .dependsOn(`stainless-scalac`)

// lazy val `stainless-dotty-frontend` = (project in file("frontends/dotty"))
//   .settings(commonSettings)
//   .settings(noPublishSettings)
//   .settings(name := "stainless-dotty-frontend")
//   .dependsOn(`stainless-core`)
//   .settings(libraryDependencies += "ch.epfl.lamp" % dottyLibrary % dottyVersion % "provided")

// lazy val `stainless-dotty` = (project in file("frontends/stainless-dotty"))
//   .enablePlugins(JavaAppPackaging)
//   .enablePlugins(BuildInfoPlugin)
//   .settings(commonSettings, commonFrontendSettings)
//   .settings(artifactSettings, scriptSettings)
//   .settings(noPublishSettings)
//   .settings(
//     name := "stainless-dotty",
//     frontendClass := "dotc.DottyCompiler",
//   )
//   .dependsOn(inox % "test->test;it->test,it")
//   .dependsOn(`stainless-dotty-frontend`)
//   .aggregate(`stainless-dotty-frontend`)
//   // Should truly depend on dotty, overriding the "provided" modifier above:
//   .settings(libraryDependencies += "ch.epfl.lamp" % dottyLibrary % dottyVersion)
//   .configs(IntegrationTest)

lazy val `sbt-stainless` = (project in file("sbt-plugin"))
  .enablePlugins(BuildInfoPlugin)
  .enablePlugins(SbtPlugin)
  .settings(baseSettings)
  .settings(publishSbtSettings)
  .settings(
    // Note: sbt-stainless is itself compiled with Scala 2.12 (as is SBT 1.x)
    description := "Plugin integrating Stainless in sbt",
    sbtPlugin := true,
    publishMavenStyle := false,
    buildInfoUsePackageAsPath := true,
    buildInfoPackage := "ch.epfl.lara.sbt.stainless",
    buildInfoKeys ++= Seq[BuildInfoKey](
      BuildInfoKey.map(version) { case (_, v) => "stainlessVersion" -> v },
      "supportedScalaVersions" -> Seq(stainlessProgScalaVersion),
      "stainlessProgScalaVersion" -> stainlessProgScalaVersion,
      "stainlessScalaVersion" -> stainlessScalaVersion,
    ),
  )
  .settings(
    scripted := scripted.tag(Tags.Test).evaluated,
    scriptedLaunchOpts ++= Seq(
      "-Xmx768m",
      "-Dplugin.version=" + version.value,
      "-Dscala.version=" + stainlessProgScalaVersion
    ),
    scriptedBufferLog := false,
    scriptedDependencies := {
      publishLocal.value
      (`stainless-library` / update).value
      (`stainless-library` / publishLocal).value
      (`stainless-scalac-plugin` / publishLocal).value
    }
  )

lazy val root = (project in file("."))
  .disablePlugins(AssemblyPlugin)
  .settings(artifactSettings, noPublishSettings)
  .settings(
    Compile / sourcesInBase := false,
  )
  .dependsOn(`stainless-scalac`, `stainless-library`/*, `stainless-dotty`*/, `sbt-stainless`)
  .aggregate(`stainless-core`, `stainless-library`, `stainless-scalac`/*, `stainless-dotty`*/, `sbt-stainless`, `stainless-scalac-plugin`)

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

