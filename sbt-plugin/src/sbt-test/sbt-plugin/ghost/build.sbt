
def commonSettings = Seq(
  version := "0.1",
  // We would like to test the sbt plugin on both Scala 3 and Scala 2
  // To avoid duplicating sbt test projects, we make use of crossScalaVersions.
  // However, we need to set scalaVersion to a value that Stainless supports
  // in order to pass through the check.
  scalaVersion := sys.props("dotty.version"),
  crossScalaVersions := Seq(sys.props("scalac.version"), sys.props("dotty.version"))
)

lazy val basic = (project in file("basic"))
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
