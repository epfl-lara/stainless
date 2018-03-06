package ch.epfl.lara.sbt.stainless

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardCopyOption
import java.util.stream.Collectors
import java.util.zip.ZipFile
import java.util.zip.ZipEntry

import sbt._
import sbt.Keys._

object StainlessPlugin extends sbt.AutoPlugin {

  private val IssueTracker = "https://github.com/epfl-lara/stainless/issues"

  override def requires: Plugins = plugins.JvmPlugin
  override def trigger: PluginTrigger = noTrigger // --> This plugin needs to be manually enabled

  object autoImport {
    val stainlessVersion = settingKey[String]("The version of stainless to use")
    val stainlessIsEnabled = settingKey[Boolean]("Flag controlling stainless verification")
  }

  import autoImport._

  /**
    * An (Ivy) configuration allowing us to manage dependencies outside of the project's classpath.
    * Using a configurations enables to fetch dependencies via `update` (see the `fetchJars` method).
    */
  private val StainlessLibSources = config("stainless-lib").hide

  override def globalSettings = Seq(
    onLoad := onLoad.value andThen checkProjectsScalaVersion
  )

  /**
    * Reports an error to the user if the `StainlessPlugin` is enabled on a module whose Scala version is unsupported.
    */
  private def checkProjectsScalaVersion(state: State): State = {
    val extracted = Project.extract(state)

    val allBuildProjects = extracted.currentUnit.defined
    for {
      (id, proj) <- allBuildProjects
      if proj.autoPlugins.toSet.contains(StainlessPlugin)
      projRef = ProjectRef(extracted.currentUnit.unit.uri, id)
      stainlessEnabled <- (stainlessIsEnabled in projRef).get(extracted.structure.data)
      if stainlessEnabled
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
    stainlessIsEnabled := true,
    autoCompilerPlugins := stainlessIsEnabled.value,
    ivyConfigurations += StainlessLibSources,
    libraryDependencies ++= stainlessModules.value,
    // You can avoid having this resolver if you set up the epfl-lara bintray organization to automatically push artifacts
    // to maven central. Read https://blog.bintray.com/2014/02/11/bintray-as-pain-free-gateway-to-maven-central/ for how.
    resolvers += Resolver.bintrayRepo("epfl-lara", "maven")
  ) ++
    inConfig(Compile)(stainlessConfigSettings) ++ // overrides settings that are scoped (by sbt) at the `Compile` configuration
    inConfig(Test)(stainlessConfigSettings) ++    // overrides settings that are scoped (by sbt) at the `Test` configuration
    inConfig(Compile)(compileSettings)            // overrides settings that are scoped (by sbt) at the `Compile` configuration

  private def stainlessModules: Def.Initialize[Seq[ModuleID]] = Def.setting {
    val library = ("ch.epfl.lara" % s"stainless-library_${scalaVersion.value}" % stainlessVersion.value).sources() % StainlessLibSources
    if (stainlessIsEnabled.value)
      Seq(
        compilerPlugin("ch.epfl.lara" % s"stainless-scalac-plugin_${scalaVersion.value}" % stainlessVersion.value),
        library
      )
    else Seq(
      // The stainless library might still be needed to compile the code even if stainless verification is disabled.
      // This because the compiled code may refer to types/annotations defined in the stainless library.
      library
    )
  }

  lazy val stainlessConfigSettings: Seq[Def.Setting[_]] = Seq(
    managedSources ++= stainlessLibrary.value
  )

  private def stainlessLibrary: Def.Initialize[Task[Seq[File]]] = Def.task {
    val log = streams.value.log
    val projectName = (name in thisProject).value

    val config = StainlessLibSources
    val sourceJars = fetchJars(update.value, config, _.classifier == Some(Artifact.SourceClassifier))
    log.debug(s"[$projectName] Configuration ${config.name} has modules: $sourceJars")

    val additionalSourceDirectories = sourceJars map { jar =>
      val name = jar.getName.dropRight(4) // drop the ".jar" extension
      val destDir = (target.value / name).toPath
      // Don't unjar every time
      if (!destDir.toFile.exists()) {
        // unjar the stainless-library-sources.jar into the `destDirectory`
        Files.createDirectories(destDir)
        unjar(jar, destDir)
        log.debug(s"[$projectName] Unzipped ${jar.getName} in $destDir")
      }
      destDir
    }

    /** Collect all .scala files in the passed `folders`.*/
    @annotation.tailrec
    def allScalaSources(sourcesSoFar: Seq[File])(folders: Seq[Path]): Seq[File] = folders match {
      case Nil => sourcesSoFar
      case folder +: rest =>
        import scala.collection.JavaConverters._
        val paths = Files.list(folder).collect(Collectors.toList()).asScala
        val dirs = paths.filter(_.toFile.isDirectory)
        val sources = for {
          path <- paths
          file = path.toFile
          if file.getName.endsWith("scala")
        } yield file
        allScalaSources(sources ++ sourcesSoFar)(dirs ++ rest)
    }

    allScalaSources(Seq.empty)(additionalSourceDirectories)
  }

  /**
    * Allows to fetch dependencies scoped to the passed configuration.
    */
  private def fetchJars(report: UpdateReport, config: Configuration, filter: Artifact => Boolean): Seq[File] = {
    val toolReport = report.configuration(config.name) getOrElse
      sys.error(s"No ${config.name} configuration found. This is a bug on sbt-stainless, please report it: $IssueTracker")

    for {
      m <- toolReport.modules
      (art, file) <- m.artifacts
      if filter(art)
    } yield file
  }

  private def unjar(jar: File, destPath: Path): Unit = {
    var archive: ZipFile = null
    try {
      archive = new ZipFile(jar)
      import scala.collection.JavaConverters._
      val entries: List[ZipEntry] = archive.stream().collect(Collectors.toList()).asScala.toList
      entries foreach { entry =>
        val entryDest = destPath.resolve(entry.getName())
        if (!entry.isDirectory()) {
          Files.createDirectories(entryDest.getParent)
          Files.copy(archive.getInputStream(entry), entryDest, StandardCopyOption.REPLACE_EXISTING)
        }
      }
    }
    finally archive.close()
  }

  private lazy val compileSettings: Seq[Def.Setting[_]] = inTask(compile)(compileInputsSettings)

  private def compileInputsSettings: Seq[Setting[_]] = {
    Seq(
      compileInputs := {
        val currentCompileInputs = compileInputs.value
        if (stainlessIsEnabled.value) {
          val additionalScalacOptions = Seq(
            // stopping after stainless because the pattern matching phase is skipped (hence binaries cannot always be produced if a phase is skipped)
            "-Ystop-after:stainless",
            // skipping pattern matching because it's not supported by stainless
            // skipping the sbt incremental compiler phases because the interact badly with stainless (especially, a NPE
            // is thrown while executing the xsbt-dependency phase because it attempts to time-travels symbol to compiler phases
            // that are run *after* the stainless phase.
            "-Yskip:patmat,xsbt-dependency,xsbt-api,xsbt-analyzer"
          )

          // FIXME: Properly merge possibly duplicate scalac options
          val allScalacOptions = additionalScalacOptions ++ currentCompileInputs.config.options
          val updatedConfig = currentCompileInputs.config.copy(options = allScalacOptions)
          currentCompileInputs.copy(config = updatedConfig)
        }
        else currentCompileInputs
      }
    )
  }
}
