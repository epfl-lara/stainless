
def commonSettings = Seq(
  version := "0.1",
  scalaVersion := sys.props("scala.version")
)

lazy val basic = (project in file("basic"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    mainClass in (Compile, run) := Some("test.Main")
  )

lazy val `actor-tests` = (project in file("actor-tests"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    mainClass in (Compile, run) := Some("Counter"),
    libraryDependencies += "com.typesafe.akka" %% "akka-actor" % "2.5.14"
  )
