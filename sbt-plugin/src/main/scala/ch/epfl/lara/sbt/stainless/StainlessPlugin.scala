package ch.epfl.lara.sbt.stainless

import sbt._
import sbt.Keys._

object StainlessPlugin extends sbt.AutoPlugin {

  private val IssueTracker = "https://github.com/epfl-lara/stainless/issues"

  override def requires: Plugins = plugins.JvmPlugin

  override def trigger: PluginTrigger = noTrigger // --> This plugin needs to be manually enabled

  object autoImport {
    val stainlessVersion = settingKey[String]("The version of stainless to use")
  }

  import autoImport._

  private val StainlessLibSources = config("stainless-lib").hide

  override def globalSettings = Seq(
    onLoad := onLoad.value andThen checkProjectsScalaVersion
  )

  private def checkProjectsScalaVersion(state: State): State = {
    val extracted = Project.extract(state)

    val allBuildProjects = extracted.currentUnit.defined
    for {
      (id, proj) <- allBuildProjects
      if proj.autoPlugins.toSet.contains(StainlessPlugin)
      projRef = ProjectRef(extracted.currentUnit.unit.uri, id)
      sv <- (scalaVersion in projRef).get(extracted.structure.data)
      if !BuildInfo.supportedScalaVersions.contains(sv)
      projName <- (name in projRef).get(extracted.structure.data)
    } {
      state.log.error(s"""[$projName] Project uses unsupported Scala version $sv. To use stainless use one of the following Scala versions: ${BuildInfo.supportedScalaVersions.mkString(",")}.""")
    }
    state
  }

  override lazy val projectSettings: Seq[Def.Setting[_]] = stainlessSettings

  lazy val stainlessSettings: Seq[sbt.Def.Setting[_]] = Seq(
    stainlessVersion := BuildInfo.stainlessVersion,
    autoCompilerPlugins := true,
    ivyConfigurations += StainlessLibSources,
    // FIXME: The pluging currently expects that a SMT solver is in the $PATH. To fix this I need to know where the scalaz3 dependency
    //        is deployed.
    libraryDependencies ++= Seq(
      compilerPlugin("ch.epfl.lara" % s"stainless-scalac-plugin_${scalaVersion.value}" % stainlessVersion.value),
      ("ch.epfl.lara" % s"stainless-library_${scalaVersion.value}" % stainlessVersion.value).sources() % StainlessLibSources
    )
  ) ++ inConfig(Compile)(compileSettings)

  private lazy val compileSettings: Seq[Def.Setting[_]] = inTask(compile)(compileInputsSettings)

  private def compileInputsSettings: Seq[Setting[_]] = {
    Seq(
      compileInputs := {
        val currentCompileInputs = compileInputs.value
        val additionalScalacOptions = stainlessExtraScalacOptions.value

        // FIXME: Properly merge possibly duplicate -sourcepath scalac options
        val allScalacOptions = additionalScalacOptions ++ currentCompileInputs.config.options
        val updatedConfig = currentCompileInputs.config.copy(options = allScalacOptions)
        currentCompileInputs.copy(config = updatedConfig)
      }
    )
  }

  private def stainlessExtraScalacOptions: Def.Initialize[Task[Seq[String]]] = Def.task {
    val config = StainlessLibSources
    val sourceJars = fetchJars(update.value, config, _.classifier == Some(Artifact.SourceClassifier))

    val projectName = (name in thisProject).value
    val log = streams.value.log
    log.debug(s"[$projectName] Configuration ${config.name} has modules: $sourceJars")

    import java.io.File.pathSeparator
    val sourcepath = Seq("-sourcepath", (sourceJars ++ sourceDirectories.value).mkString(pathSeparator))

    log.debug(s"[$projectName] Extra scalacOptions injected by stainless: ${sourcepath.mkString(" ")}.")
    sourcepath
  }

  // allows to fetch dependencies scoped to the passed configuration
  private def fetchJars(report: UpdateReport, config: Configuration, filter: Artifact => Boolean): Seq[File] = {
    val toolReport = report.configuration(config.name) getOrElse
      sys.error(s"No ${config.name} configuration found. This is a bug on sbt-stainless, please report it: $IssueTracker")

    for {
      m <- toolReport.modules
      (art, file) <- m.artifacts
      if filter(art)
    } yield file
  }
}
