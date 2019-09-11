
def commonSettings = Seq(
  version := "0.1",
  scalaVersion := sys.props("scala.version")
)

val unsupportedScalaVersion = "2.11.7"

val checkScalaFailures = taskKey[Unit]("checkScalaFailures")
val assertLogMessage = taskKey[Unit]("checks a log message emitted")

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

def checkScalaFailuresTask(expectedErrorMessage: String) = Def.task {
  val reporter = savedReporter.value
  val ignore = (compile in Compile).failure.value
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
