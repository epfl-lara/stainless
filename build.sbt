name := "stainless"

version := "0.1"

organization := "ch.epfl.lara"

val scalaVer = "2.11.8"

scalaVersion := "2.11.8"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature"
)

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", baseDirectory.value+"/src/main/scala/root-doc.txt")

site.settings

site.sphinxSupport()

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.typesafe.com/typesafe/releases/",
  "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots",
  "Sonatype OSS Releases" at "https://oss.sonatype.org/content/repositories/releases"
)

libraryDependencies ++= Seq(
  "ch.epfl.lamp" %% "dotty" % "0.1-SNAPSHOT",
  "org.scalatest" %% "scalatest" % "2.2.4" % "test;it",
  "com.typesafe.akka" %% "akka-actor" % "2.3.4",
  "org.ow2.asm" % "asm-all" % "5.0.4",
  "com.fasterxml.jackson.module" %% "jackson-module-scala" % "2.6.0-rc2",
  "org.apache.commons" % "commons-lang3" % "3.4"
  //"com.regblanc" %% "scala-smtlib" % "0.2"
)

lazy val scriptName = "stainless"

lazy val scriptFile = file(".") / scriptName

clean := {
  clean.value
  if (scriptFile.exists && scriptFile.isFile) {
    scriptFile.delete
  }
}

lazy val script = taskKey[Unit]("Generate the stainless Bash script")

script := {
  val s = streams.value
  try {
    val cps = (dependencyClasspath in Compile).value
    val out = (classDirectory      in Compile).value
    val res = (resourceDirectory   in Compile).value

    if (scriptFile.exists) {
      s.log.info("Regenerating '" + scriptFile.getName + "' script")
      scriptFile.delete
    } else {
      s.log.info("Generating '" + scriptFile.getName + "' script")
    }

    val paths = (res.getAbsolutePath +: out.getAbsolutePath +: cps.map(_.data.absolutePath)).mkString(System.getProperty("path.separator"))
    IO.write(scriptFile, s"""|#!/bin/bash --posix
                            |
                            |SCALACLASSPATH=$paths
                            |
                            |java -Xmx2G -Xms512M -Xss64M -classpath "$${SCALACLASSPATH}" -Dscala.usejavacp=false stainless.Main $$@ 2>&1 | tee -i last.log
                            |""".stripMargin)
    scriptFile.setExecutable(true)
  } catch {
    case e: Throwable =>
      s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
  }
}

Keys.fork in run := true

testOptions in Test := Seq(Tests.Argument("-oDF"))

testOptions in IntegrationTest := Seq(Tests.Argument("-oDF"))

def ghProject(repo: String, version: String) = RootProject(uri(s"${repo}#${version}"))

lazy val inox = //ghProject("https://github.com/epfl-lara/inox.git", "fbbca114a8d7af021bc20d677ad2cf0e2e3a411a")
  RootProject(file("../inox"))

lazy val root = (project in file("."))
  .configs(IntegrationTest)
  .settings(Defaults.itSettings : _*)
//  .settings(inConfig(IntegrationTest)(Defaults.testTasks ++ Seq(
//    logBuffered := false,
//    parallelExecution := false
//  )) : _*)
//  .dependsOn(bonsai)
  .dependsOn(inox)

