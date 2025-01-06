
def commonSettings = Seq(
  version := "0.1",
  scalaVersion := sys.props("dotty.version")
)

lazy val basic = (project in file("basic"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    Compile / run / mainClass := Some("test.Main")
  )

lazy val tailrec = (project in file("tailrec"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    Compile / run / mainClass := Some("test.Main")
  )

lazy val `actor-tests` = (project in file("actor-tests"))
  .enablePlugins(StainlessPlugin)
  .settings(commonSettings)
  .settings(
    Compile / run / mainClass := Some("Counter"),
    libraryDependencies += ("com.typesafe.akka" %% "akka-actor" % "2.5.32").cross(CrossVersion.for3Use2_13)
  )
