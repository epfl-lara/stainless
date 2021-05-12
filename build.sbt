import sbt.ScriptedPlugin

enablePlugins(GitVersioning)
enablePlugins(GitBranchPrompt)

git.useGitDescribe := true

val osInf = Option(System.getProperty("os.name")).getOrElse("")

val isUnix    = osInf.indexOf("nix") >= 0 || osInf.indexOf("nux") >= 0
val isWindows = osInf.indexOf("Win") >= 0
val isMac     = osInf.indexOf("Mac") >= 0

val osName = if (isWindows) "win" else if (isMac) "mac" else "unix"
val osArch = System.getProperty("sun.arch.data.model")

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

val SupportedScalaVersions = Seq("2.12.13")

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
  skip in publish := true,
)

lazy val baseSettings: Seq[Setting[_]] = Seq(
  organization := "ch.epfl.lara",
  licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html"))
)

lazy val artifactSettings: Seq[Setting[_]] = baseSettings ++ Seq(
  scalaVersion := crossScalaVersions.value.head,
  crossScalaVersions := SupportedScalaVersions,

  buildInfoPackage := "stainless",
  buildInfoKeys := stainlessBuildInfoKeys,
  buildInfoOptions := Seq(BuildInfoOption.BuildTime),
)

// FIXME: Uncomment this when we are are able to upgrade sbt version
// Global / excludeLintKeys ++= Set(
//   buildInfoPackage,
//   buildInfoKeys,
//   buildInfoOptions,
//   testOptions
// )

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
    "ch.epfl.lara"    %% "cafebabe"      % "1.2",
    "uuverifiers"     %% "princess"      % "2018-02-26" ,
    "io.circe"        %% "circe-core"    % circeVersion,
    "io.circe"        %% "circe-generic" % circeVersion,
    "io.circe"        %% "circe-parser"  % circeVersion,
    "io.get-coursier" %% "coursier"      % "2.0.0-RC4-1",
    "com.typesafe"     % "config"        % "1.3.4",

    "org.scalatest"   %% "scalatest"     % "3.2.7" % "test",
  ),

  // disable documentation packaging in universal:stage to speedup development
  Compile / packageDoc / mappings := Seq(),

  Global / concurrentRestrictions += Tags.limitAll(nParallel),

  Compile / sourcesInBase := false,

  run / Keys.fork := true,

  run / javaOptions ++= Seq(
    "-Xss256M",
    "-Xms1024M",
    "-XX:MaxMetaspaceSize=512M",
    "-XX:+UseCodeCacheFlushing",
    "-XX:ReservedCodeCacheSize=256M",
  ),

  /* run / javaOptions += "-agentlib:jdwp=transport=dt_socket,server=y,suspend=y,address=5005", */

  Test / testOptions := Seq(Tests.Argument("-oDF")),

  IntegrationTest / testOptions := Seq(Tests.Argument("-oDF")),

  ThisBuild / maxErrors := 5
)

lazy val assemblySettings: Seq[Setting[_]] = {
  def isNativeLib(file: String): Boolean =
    file.endsWith("dll") || file.endsWith("so") || file.endsWith("jnilib")

  Seq(
    assembly / assemblyMergeStrategy := {
      // The BuildInfo class file from the current project comes before the one from `stainless-scalac`,
      // hence the following merge strategy picks the standalone BuildInfo over the usual one.
      case "stainless/BuildInfo.class" => MergeStrategy.first
      case "stainless/BuildInfo$.class" => MergeStrategy.first
      case PathList("META-INF", xs @ _*) => MergeStrategy.discard
      case PathList("scala", "collection", "compat", _*) => MergeStrategy.first
      case PathList("scala", "annotation", _*) => MergeStrategy.first
      case PathList("scala", "util", _*) => MergeStrategy.first
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
  val libFiles = ((root.base / "frontends" / "library") ** "*.scala").get
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
          |  val extraClasspath = \"\"\"${removeSlashU(extraClasspath.value)}\"\"\"
          |  val extraCompilerArguments = List("-classpath", \"\"\"${removeSlashU(extraClasspath.value)}\"\"\")
          | 
          |  val defaultPaths = List(${removeSlashU(libraryFiles.map(_._1).mkString("\"\"\"", "\"\"\",\n \"\"\"", "\"\"\""))})
          |  val libPaths = try {
          |    val source = scala.io.Source.fromFile(\"${libFilesFile}\")
          |    try source.getLines.toList finally source.close()
          |  } catch {
          |     case (_:Throwable) => defaultPaths
          |  }
          |
          |  override val factory = new frontends.${frontendClass.value}.Factory(extraCompilerArguments, libPaths)
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

// lazy val inox = RootProject(file("../inox"))
lazy val inox = ghProject("https://github.com/epfl-lara/inox.git", "7e72d941e748df31b966bbb5726ade447673b199")
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

lazy val `stainless-library` = (project in file("frontends") / "library")
  .disablePlugins(AssemblyPlugin)
  .settings(commonSettings, publishMavenSettings)
  .settings(
    name := "stainless-library",

    // don't publish binaries - stainless-library is only consumed as a sources component
    publishArtifact in packageBin := false,
    crossVersion := CrossVersion.binary,
    scalaSource in Compile := baseDirectory.value
  )

lazy val `stainless-algebra` = (project in file("frontends") / "algebra")
  .disablePlugins(AssemblyPlugin)
  .settings(commonSettings, publishMavenSettings)
  .settings(
    name := "stainless-algebra",
    version := "0.1.2",

    // don't publish binaries - stainless-algebra is only consumed as a sources component
    publishArtifact in packageBin := false,
    crossVersion := CrossVersion.binary,
    scalaSource in Compile := baseDirectory.value,
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
    libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value,
    buildInfoKeys ++= Seq[BuildInfoKey]("useJavaClassPath" -> false),
    assemblyOption in assembly := (assemblyOption in assembly).value.copy(includeScala = false),
    assemblyExcludedJars in assembly := {
      val cp = (fullClasspath in assembly).value
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
    packageBin in Compile := (assembly in (`stainless-scalac`, Compile)).value
  )

lazy val `stainless-scalac-standalone` = (project in file("frontends") / "stainless-scalac-standalone")
  .enablePlugins(BuildInfoPlugin)
  .enablePlugins(JavaAppPackaging)
  .settings(artifactSettings, assemblySettings)
  .settings(
    name := "stainless-scalac-standalone",
    buildInfoKeys ++= Seq[BuildInfoKey]("useJavaClassPath" -> true),
    (mainClass in assembly) := Some("stainless.Main"),
    (assemblyJarName in assembly) := (name.value + "-" + version.value + ".jar"),
    (unmanagedJars in Runtime) := (unmanagedJars in (`stainless-scalac`, Runtime)).value
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
    description := "Plugin integrating Stainless in sbt",
    sbtPlugin := true,
    publishMavenStyle := false,
    buildInfoUsePackageAsPath := true,
    buildInfoPackage := "ch.epfl.lara.sbt.stainless",
    buildInfoKeys ++= Seq[BuildInfoKey](
      BuildInfoKey.map(version) { case (_, v) => "stainlessVersion" -> v },
      "supportedScalaVersions" -> SupportedScalaVersions,
    ),
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
      (update       in `stainless-library`).value
      (publishLocal in `stainless-library`).value
      (publishLocal in `stainless-scalac-plugin`).value
    }
  )

lazy val root = (project in file("."))
  .disablePlugins(AssemblyPlugin)
  .settings(artifactSettings, noPublishSettings)
  .settings(
    sourcesInBase in Compile := false,
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

