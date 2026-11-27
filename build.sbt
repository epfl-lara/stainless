import sbt.ScriptedPlugin

enablePlugins(GitVersioning)
enablePlugins(GitBranchPrompt)

git.useGitDescribe := true
// sbt-git 3 scopes the public alias to the project; inherited versions need this too.
ThisBuild / git.useGitDescribe := true
useJGitOnlyForReads

// Keep the seven-character descriptions used by the packaging scripts instead of
// modern JGit's adaptive abbreviation length.
ThisBuild / git.gitDescribedVersion := {
  val patterns = (ThisBuild / git.gitDescribePatterns).value
  val tagToVersion = (ThisBuild / git.gitTagToVersionNumber).value
  val repo = new org.eclipse.jgit.storage.file.FileRepositoryBuilder()
    .findGitDir((ThisBuild / baseDirectory).value).build()
  try {
    scala.util.Try(Option(new org.eclipse.jgit.api.Git(repo).describe()
      .setTags(true).setAbbrev(7).setMatch(patterns: _*).call()))
      .toOption.flatten.map(v => tagToVersion(v).getOrElse(v))
  } finally repo.close()
}

Global / excludeLintKeys += buildInfoKeys
Global / excludeLintKeys += buildInfoOptions
Global / excludeLintKeys += buildInfoPackage
Global / excludeLintKeys += testOptions
Global / excludeLintKeys += publishArtifact

val circeVersion = "0.14.1"

// The number of test suites (e.g. VerificationSuite, UncheckedSuite) run in parallel
// Note that this does not dictate the parallelism per test case (e.g. verification/valid/AbstractPost.scala,
// verification/valid/AbstractRefinementMap$.scala) which is instead set with -Dtestcase-parallelism=<...>
// The property is the one that Inox's build reads: Inox is loaded as part of this build and sets
// `Global / concurrentRestrictions` too, replacing the definition below, so both must compute the same limit.
lazy val nTestSuiteParallelism = {
  val p = System.getProperty("test-parallelism")
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

// The Scala version with which Stainless (and its library) is compiled, and which is bundled as the frontend compiler.
// Note: in case of version bump, do not forget to update the `test` files in `sbt-plugin` (for `sbt scripted`)!
val stainlessScalaVersion = "3.10.1-RC1-bin-20260903-e1f9361-NIGHTLY"

val laraOrganization = "ch.epfl.lara"

scalaVersion := stainlessScalaVersion

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
  organization := laraOrganization,
  licenses := Seq("Apache-2.0" -> url("https://www.apache.org/licenses/LICENSE-2.0.html")),
  scalaOrganization := laraOrganization,
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
  // Stainless runs on Java 21 and later, whatever the JDK it is built with.
  scalacOptions ++= Seq("-release", "21"),
  javacOptions ++= Seq("--release", "21"),

  resolvers += ("uuverifiersStainless" at "https://eldarica.org/maven"),

  libraryDependencies ++= Seq(
    // "ch.epfl.lara"    %% "inox"          % inoxVersion,
    // "ch.epfl.lara"    %% "inox"          % inoxVersion % "test" classifier "tests",
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
    ExclusionRule("org.scala-lang.modules", "scala-xml_3"),
    // These are required because we use a custom scalaOrganization and want a single
    // version of the Scala library in the classpath. Without it, SBT would pull an
    // org.scala-lang library from transitive dependencies as well.
    ExclusionRule("org.scala-lang", "scala3-library_3"),
    ExclusionRule("org.scala-lang", "scala3-compiler_3"),
    ExclusionRule("org.scala-lang", "scala-library"),
  ),

  // disable documentation packaging in Universal/stage to speedup development
  Compile / packageDoc / mappings := Seq(),

  Compile / sourcesInBase := false,

  run / Keys.fork := true,

  run / javaOptions ++= Seq(
    // The native Z3 interface loads Z3 through JNI, which Java 22+ warns about otherwise.
    "--enable-native-access=ALL-UNNAMED",
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
    "-feature",
    "-language:experimental.qualifiedTypes"
  ),

  // disable documentation packaging in Universal/stage to speedup development
  Compile / packageDoc / mappings := Seq(),

  Compile / sourcesInBase := false,

  run / Keys.fork := true,

  run / javaOptions ++= Seq(
    // The native Z3 interface loads Z3 through JNI, which Java 22+ warns about otherwise.
    "--enable-native-access=ALL-UNNAMED",
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
      // The licenses of Z3, bundled with the native Z3 interface (ScalaZ3)
      case PathList("META-INF", "z3", _*) => MergeStrategy.first
      case PathList("META-INF", xs @ _*) => MergeStrategy.discard
      // Java module descriptors (e.g. from the ASM jars pulled in by the Scala 3 compiler) are irrelevant in a fat jar
      case "module-info.class" => MergeStrategy.discard
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
    // Keep a single Scala library in the assembled classpath. We use a custom
    // scalaOrganization (ch.epfl.lara), but transitive dependencies still pull
    // upstream org.scala-lang Scala libraries; assembling them alongside the
    // fork's library yields conflicting scala/* classes from different Scala
    // versions. commonSettings already excludes these, but the assembling
    // projects (e.g. stainless-dotty-standalone) don't use commonSettings.
    excludeDependencies ++= Seq(
      ExclusionRule("org.scala-lang", "scala3-library_3"),
      ExclusionRule("org.scala-lang", "scala3-compiler_3"),
      ExclusionRule("org.scala-lang", "scala-library"),
    ),
  )
}

// The Stainless library sources, shipped as resources and passed to the bundled compiler at runtime.
def libraryFiles(baseDir: File): Seq[(String, File)] = {
  // Note baseDir is frontends/dotty, so we need to go up two levels with / .. / .. /
  val libFiles = ((baseDir / ".." / ".." / "frontends" / "library" / "stainless") ** "*.scala").get
  val dropCount = (libFiles.head.getPath indexOfSlice "library") + ("library".size + 1 /* for separator */)
  libFiles.map(file => (file.getPath drop dropCount, file)) // Drop the prefix of the path (i.e. everything before "library")
}

lazy val frontendSettings: Seq[Setting[_]] = inConfig(IntegrationTest)(Defaults.testSettings) ++ Seq(

  // The stainless library is compiled with qualified types enabled, which marks all its
  // definitions @experimental; referencing them requires experimental mode here as well.
  scalacOptions += "-language:experimental.qualifiedTypes",

  /**
    * NOTE: IntelliJ seems to have trouble including resources located outside the base directory of an
    *   sbt project. You can temporarily disable the following line when importing the project.
    * NOTE 2: baseDirectory.value is frontends/dotty, so we need to go up two levels with / .. / .. /
    */
  IntegrationTest / unmanagedResourceDirectories += (baseDirectory.value / ".." / ".." / "frontends" / "benchmarks"),

  // Ship the Stainless library sources as resources, along with the stainless/libfiles.txt
  // index that stainless.Main reads to locate them.
  // We have to use managed resources here to keep sbt's source watcher happy.
  Compile / resourceGenerators += Def.task {
    val libFiles = libraryFiles(baseDirectory.value)
    val resourceDir = (Compile / resourceManaged).value
    val copies = for ((libPath, libFile) <- libFiles) yield {
      val resourceFile = resourceDir / libPath
      IO.write(resourceFile, IO.read(libFile))
      resourceFile
    }
    val index = resourceDir / "stainless" / "libfiles.txt"
    IO.write(index, libFiles.map(_._1).mkString("\n"))
    index +: copies
  }.taskValue,

  assembly / test := {}, // Skip the test during assembly
) ++
  inConfig(IntegrationTest)(Defaults.testTasks ++ Seq(
    logBuffered := (nTestSuiteParallelism > 1),
    parallelExecution := (nTestSuiteParallelism > 1),
  ))

Global / concurrentRestrictions := Seq(
  Tags.limit(Tags.Test, nTestSuiteParallelism)
)

lazy val inox = RootProject(file("./inox"))

// Allow integration test to use facilities from regular tests
lazy val IntegrationTest = config("it") extend(Test)

lazy val `stainless-core` = (project in file("core"))
  .disablePlugins(AssemblyPlugin)
  .enablePlugins(BuildInfoPlugin)
  //.enablePlugins(SphinxPlugin)
  .settings(name := "stainless-core")
  // Not published to Maven Central (no `publishTo`): it depends on Inox, which is built from
  // source. The compiler plugin, which is published, bundles it.
  .settings(commonSettings)
  .settings(
    // The JVM bytecode library of the code generation evaluator (CodeGenEvaluator)
    libraryDependencies += "ch.epfl.lara" %% "cafebabe" % "1.3.0",
  )
  //.settings(site.settings)
  .dependsOn(inox % "compile->compile;test->test")

lazy val `stainless-library` = (project in file("frontends") / "library")
  .disablePlugins(AssemblyPlugin)
  .settings(stainlessLibSettings, publishMavenSettings)
  .settings(
    name := "stainless-library",
    description := "The Stainless library: the specification constructs, annotations and verified data structures of the Stainless verification framework",
    scalaVersion := stainlessScalaVersion,
    crossVersion := CrossVersion.binary,
    Compile / scalaSource := baseDirectory.value / "stainless"
  )

lazy val `stainless-algebra` = (project in file("frontends") / "algebra")
  .disablePlugins(AssemblyPlugin)
  .settings(stainlessLibSettings)
  .settings(
    name := "stainless-algebra",
    version := "0.1.2",
    scalaVersion := stainlessScalaVersion,
    // don't publish binaries - stainless-algebra is only consumed as a sources component
    packageBin / publishArtifact := false,
    crossVersion := CrossVersion.binary,
    Compile / scalaSource := baseDirectory.value / "stainless"
  )
  .dependsOn(`stainless-library`)

lazy val `stainless-dotty` = (project in file("frontends/dotty"))
  .enablePlugins(JavaAppPackaging)
  .enablePlugins(BuildInfoPlugin)
  .settings(commonSettings, frontendSettings)
  .settings(assemblySettings)
  .settings(noPublishSettings)
  .settings(
    name := "stainless-dotty",
    // Check the launcher's JDK at runtime, after processing -java-home.
    bashScriptExtraDefines += """process_my_args() {
  local runtime_java_version
  runtime_java_version=$("$java_cmd" -version 2>&1 | awk -F '"' '/version/ {print $2; exit}')
  if [[ "$runtime_java_version" =~ ^([0-9]+) ]] && [[ "${BASH_REMATCH[1]}" -ge 25 ]]; then
    # Prepend the default so explicit JVM options can override it.
    java_args=("-XX:+UseCompactObjectHeaders" "${java_args[@]}")
  fi
  # The native Z3 interface loads Z3 through JNI, which Java 22+ warns about otherwise.
  java_args=("--enable-native-access=ALL-UNNAMED" "${java_args[@]}")
  residual_args=("$@")
}
""",
    libraryDependencies += laraOrganization %% "scala3-compiler" % stainlessScalaVersion,
    buildInfoKeys ++= Seq[BuildInfoKey]("useJavaClassPath" -> false),
    // We include Scala library to be certain we also include scala-parser-combinators (which is not shipped with the Scala std library)
    assemblyPackageScala / assembleArtifact := true,
    // The native Z3 interface (ScalaZ3) is platform-independent: it bundles the native libraries of
    // Z3 for all platforms. It is part of the assembly, so that the compiler plugin needs no solver
    // on the PATH (at the cost of 55MB).
    assembly / assemblyExcludedJars := Seq(),
  )
  .dependsOn(`stainless-core`)
  .dependsOn(`stainless-library`)
  .dependsOn(inox % "test->test;it->test,it")
  .configs(IntegrationTest)

lazy val `stainless-dotty-plugin` = (project in file("frontends") / "stainless-dotty-plugin")
  .settings(artifactSettings, publishMavenSettings, assemblySettings)
  .settings(
    name := "stainless-dotty-plugin",
    description := "The Stainless verification framework, as a plugin of the Scala 3 compiler",
    crossVersion := CrossVersion.full, // because compiler api is not binary compatible
    Compile / packageBin := (`stainless-dotty` / Compile / assembly).value
  )

lazy val `stainless-dotty-standalone` = (project in file("frontends") / "stainless-dotty-standalone")
  .enablePlugins(BuildInfoPlugin)
  .enablePlugins(JavaAppPackaging)
  .settings(artifactSettings, assemblySettings)
  .settings(
    name := "stainless-dotty-standalone",
    buildInfoKeys ++= Seq[BuildInfoKey]("useJavaClassPath" -> true),
    assembly / mainClass := Some("stainless.Main"),
    assembly / assemblyJarName := (name.value + "-" + version.value + ".jar"),
    Runtime / unmanagedJars := (`stainless-dotty` / Runtime / unmanagedJars).value,
    assemblyPackageScala / assembleArtifact := true,
    assembly / assemblyExcludedJars := Seq(),
  )
  .dependsOn(`stainless-dotty`)

lazy val `sbt-stainless` = (project in file("sbt-plugin"))
  .enablePlugins(BuildInfoPlugin)
  .enablePlugins(SbtPlugin)
  .settings(baseSettings)
  .settings(
    // Note: sbt-stainless is itself compiled with Scala 2.12 (as is SBT 1.x)
    description := "Plugin integrating Stainless in sbt",
    sbtPlugin := true,
    publishMavenStyle := false,
    buildInfoUsePackageAsPath := true,
    buildInfoPackage := "ch.epfl.lara.sbt.stainless",
    buildInfoKeys ++= Seq[BuildInfoKey](
      BuildInfoKey.map(version) { case (_, v) => "stainlessVersion" -> v },
      "supportedScalaVersions" -> Seq(stainlessScalaVersion),
      "stainlessScalaVersion" -> stainlessScalaVersion,
      "stainlessLibScalaVersion" -> stainlessScalaVersion,
    ),
    // Compiled with Scala 2; don't use the custom scalaOrganization
    scalaOrganization := "org.scala-lang",
  )
  .settings(
    scripted := scripted.tag(Tags.Test).evaluated,
    scriptedLaunchOpts ++= Seq(
      "-Xmx768m",
      "-Dplugin.version=" + version.value,
      "-Ddotty.version=" + stainlessScalaVersion
    ) ++ sys.props.get("sbt.ivy.home").map("-Dsbt.ivy.home=" + _), // where scriptedDependencies publishes
    scriptedBufferLog := false,
    scriptedDependencies := {
      publishLocal.value
      (`stainless-library` / update).value
      (`stainless-library` / publishLocal).value
      (`stainless-dotty-plugin` / publishLocal).value
    }
  )

lazy val root = (project in file("."))
  .disablePlugins(AssemblyPlugin)
  .settings(artifactSettings, noPublishSettings)
  .settings(
    Compile / sourcesInBase := false,
  )
  .dependsOn(`stainless-library`, `stainless-dotty`, `sbt-stainless`)
  .aggregate(`stainless-core`, `stainless-library`, `stainless-dotty`, `sbt-stainless`, `stainless-dotty-plugin`)

// Publishing to Maven Central (see .github/workflows/stainless-release.yml). Only the Stainless
// library (ch.epfl.lara:stainless-library_3) and the compiler plugin
// (ch.epfl.lara:stainless-dotty-plugin_<Scala version>) are published there. The version comes
// from the latest tag, through `git describe` (sbt-git): v0.11.0 gives 0.11.0, and -SNAPSHOT is
// appended when the working tree has uncommitted changes.
// `sbt stainless-library/publishSigned stainless-dotty-plugin/publishSigned` signs the artifacts
// and stages them locally (in target/sona-staging), `sbt sonaRelease` uploads them to the Central
// Portal and releases them (`sbt sonaUpload` only uploads them, to inspect them in the Portal
// first). Both read the Portal token from SONATYPE_USERNAME and SONATYPE_PASSWORD.
def publishMavenSettings: Seq[Setting[_]] = Seq(
  homepage := Some(url("https://epfl-lara.github.io/stainless/")),
  scmInfo := Some(ScmInfo(
    url("https://github.com/epfl-lara/stainless"),
    "scm:git:git@github.com:epfl-lara/stainless.git",
  )),
  developers := List(
    Developer("epfl-lara", "EPFL Lab for Automated Reasoning and Analysis", "lara.maven@epfl.ch", url("https://lara.epfl.ch")),
  ),
  publishMavenStyle := true,
  Test / publishArtifact := false,
  pomIncludeRepository := { _ => false },
  publishTo := localStaging.value,
  // The key that signs the artifacts, when the keyring holds several
  pgpSigningKey := sys.env.get("PGP_FINGERPRINT"),
)

// FIXME assembly should be disabled at the top level, but isn't
