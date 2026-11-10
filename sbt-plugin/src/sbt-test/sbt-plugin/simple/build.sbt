
// Also sets the Scala version of the root project, which otherwise falls back to the one of sbt with a warning
ThisBuild / scalaVersion := sys.props("dotty.version")

def commonSettings = Seq(
  version := "0.1"
)

val unsupportedScalaVersion = "2.11.7"

val checkScalaFailures = taskKey[Unit]("checkScalaFailures")
val assertLogMessage = taskKey[Unit]("checks a log message emitted")
val checkExtraResolvers = taskKey[Unit]("checks that the resolvers of stainlessExtraResolvers are added to the resolvers")

val extraResolver = "extra-resolver" at "https://example.org/maven"

assertLogMessage := checkLogContains(
  s"Project uses unsupported Scala version: $unsupportedScalaVersion."
).value

lazy val success = (project in file("success"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)

lazy val failure = (project in file("failure"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(checkScalaFailures := checkScalaFailuresTask("Unexpected `require`.").value)

// This is a project on which the Stainless plugin is not enabled and hence the unsupported Scala version error should NOT be reported
lazy val ignore = (project in file("ignore"))
  .settings(scalaVersion := unsupportedScalaVersion)

// This is a project on which the Stainless plugin is enabled and it's using an unsupported Scala version. Hence, an error should be reported
lazy val unsupported = (project in file("unsupported"))
  .enablePlugins(StainlessPlugin)
  .settings(scalaVersion := unsupportedScalaVersion)

// This is a project with an extra resolver, which should be added to its resolvers to fetch `stainlessExtraDeps`
lazy val extraResolvers = (project in file("extraResolvers"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    stainlessExtraResolvers += extraResolver,
    checkExtraResolvers := {
      val rs = resolvers.value
      assert(rs.contains(extraResolver), s"Resolvers should contain $extraResolver, but are: ${rs.mkString(", ")}")
    }
  )

def checkScalaFailuresTask(expectedErrorMessage: String) = Def.task {
  val reporter = savedReporter.value
  val _ = (Compile / compile).failure.value
  val ps = reporter.problems
  assert(!ps.isEmpty, "Failed to report any problems!")
  val first = ps(0)
  assert(first.message == expectedErrorMessage, s"Reported error doesn't match. Expected `$expectedErrorMessage` but was `${first.message}`.")
}

def checkLogContains(message: String) = Def.task {
  val lastLog: File = BuiltinCommands.lastLogFile(state.value).get
  val last: String = IO.read(lastLog)
  if (!last.contains(message))
    sys.error(s"sbt output does not contain expected log message: `$message`")
  else
    IO.write(lastLog, "") // clear the backing log for for 'last'.
}
