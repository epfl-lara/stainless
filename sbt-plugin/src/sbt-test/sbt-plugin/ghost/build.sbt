
def commonSettings = Seq(
  version := "0.1",
  scalaVersion := sys.props("scala.version")
)

lazy val basic = (project in file("basic"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    Compile / run / mainClass := Some("test.Main"),
  )

lazy val `actor-tests` = (project in file("actor-tests"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    Compile / run / mainClass := Some("Counter"),
    libraryDependencies += "com.typesafe.akka" %% "akka-actor" % "2.5.14"
  )
