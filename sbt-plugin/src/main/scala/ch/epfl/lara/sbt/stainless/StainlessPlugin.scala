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
  private val stainlessScalaVersion = BuildInfo.stainlessScalaVersion
  // e.g. for 2.13.6, this would yield 2.13
  private val stainlessProgScalaBinaryVersion = CrossVersion.binaryScalaVersion(BuildInfo.stainlessProgScalaVersion)

  override def requires: Plugins = plugins.JvmPlugin
  override def trigger: PluginTrigger = noTrigger // This plugin needs to be manually enabled

  object autoImport {
    val stainlessVersion        = settingKey[String]("The version of stainless to use")
    val stainlessEnabled        = settingKey[Boolean]("Enable stainless")
    val stainlessExtraDeps      = settingKey[Seq[sbt.librarymanagement.ModuleID]]("Extra source dependencies to pass along to Stainless")
    val stainlessExtraResolvers = settingKey[Seq[sbt.librarymanagement.MavenRepository]]("Extra resolvers to pass along to Stainless")
  }

  import autoImport._

  /**
    * An (Ivy) configuration allowing us to manage dependencies outside of the project's classpath.
    * Using a configurations enables to fetch dependencies via `update` (see the `fetchJars` method).
    */
  private val StainlessLibSources = config("stainless-lib").hide

  override def globalSettings = Seq(
    onLoad := onLoad.value andThen checkProjectsScalaVersion,
    stainlessExtraResolvers := Seq(Resolver.sonatypeRepo("releases"))
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
      sv <- (projRef / scalaVersion).get(extracted.structure.data)
      if !BuildInfo.supportedScalaVersions.contains(sv)
    } state.log.error(
      s"Project uses unsupported Scala version: $sv. " +
      s"Stainless supports the following Scala version: ${BuildInfo.supportedScalaVersions.mkString(", ")}."
    )
    state
  }

  override lazy val projectSettings: Seq[Def.Setting[_]] = stainlessSettings

  lazy val stainlessSettings: Seq[sbt.Def.Setting[_]] = Seq(
    stainlessVersion        := BuildInfo.stainlessVersion,
    stainlessEnabled        := true,
    stainlessExtraDeps      := Seq.empty,
    autoCompilerPlugins     := true,
    ivyConfigurations       += StainlessLibSources,
    libraryDependencies    ++= stainlessModules.value,

    // You can avoid having this resolver if you set up the epfl-lara bintray organization to automatically push artifacts
    // to maven central. Read https://blog.bintray.com/2014/02/11/bintray-as-pain-free-gateway-to-maven-central/ for how.
    resolvers ++= Seq(
      Resolver.bintrayRepo("epfl-lara", "maven"),
      Resolver.bintrayRepo("epfl-lara", "princess"),
      Resolver.bintrayIvyRepo("epfl-lara", "sbt-plugins"),
      ("uuverifiers" at "http://logicrunch.research.it.uu.se/maven").withAllowInsecureProtocol(true),
    )
  ) ++
    inConfig(Compile)(stainlessConfigSettings) ++ // overrides settings that are scoped (by sbt) at the `Compile` configuration
    inConfig(Test)(stainlessConfigSettings) ++    // overrides settings that are scoped (by sbt) at the `Test` configuration
    inConfig(Compile)(compileSettings)            // overrides settings that are scoped (by sbt) at the `Compile` configuration

  private def stainlessModules: Def.Initialize[Seq[ModuleID]] = Def.setting {
    val pluginRef  = "ch.epfl.lara" % s"stainless-scalac-plugin_$stainlessScalaVersion" % stainlessVersion.value
    val libraryRef = "ch.epfl.lara" % s"stainless-library_$stainlessProgScalaBinaryVersion" % stainlessVersion.value

    val sourceDeps = (libraryRef +: stainlessExtraDeps.value).map { dep =>
      dep.intransitive().sources() % StainlessLibSources
    }

    compilerPlugin(pluginRef) +: sourceDeps
  }

  lazy val stainlessConfigSettings: Seq[Def.Setting[_]] = Seq(
    managedSources ++= fetchAndUnzipSourceDeps.value,
    managedSourceDirectories += stainlessSourcesLocation.value
  )

  private def stainlessSourcesLocation = Def.setting {
    target.value / s"stainless_$stainlessProgScalaBinaryVersion"
  }

  private def fetchAndUnzipSourceDeps: Def.Initialize[Task[Seq[File]]] = Def.task {
    val log = streams.value.log
    val projectName = (thisProject / name).value

    val config = StainlessLibSources
    val sourceJars = fetchJars(
      updateClassifiers.value,
      config,
      artifact => artifact.classifier.contains(Artifact.SourceClassifier)
    ).distinct

    log.debug(s"[$projectName] Configuration ${config.name} has modules: ${sourceJars.mkString(", ")}")

    val destDir = stainlessSourcesLocation.value
    if (!destDir.exists) {
      Files.createDirectories(destDir.toPath)
    }

    val additionalSourceDirectories = sourceJars map { jar =>
      val subDir = jar.getName.stripSuffix(".jar")
      val subDestDir = destDir.toPath.resolve(subDir).toFile

      // Don't unjar every time
      if (!subDestDir.exists()) {
        Files.createDirectories(subDestDir.toPath)
        unjar(jar, subDestDir.toPath)
        log.debug(s"[$projectName] UnJARed ${jar.getName} in $subDestDir")
      }

      subDestDir.toPath
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
    val toolReport = report.configuration(config.toConfigRef) getOrElse {
      sys.error(s"No ${config.name} configuration found. $reportBugText")
    }

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

        val additionalScalacOptions = Seq(
          // skipping the sbt incremental compiler phases because the interact badly with stainless (especially, a NPE
          // is thrown while executing the xsbt-dependency phase because it attempts to time-travels symbol to compiler phases
          // that are run *after* the stainless phase.
          "-Yskip:xsbt-dependency,xsbt-api,xsbt-analyzer",

          // Here we tell the stainless plugin whether or not to enable verification
          s"-P:stainless:verify:${stainlessEnabled.value}",

          // For now we always enable ghost elimination
          "-P:stainless:ghost-elim:true",
        )

        // FIXME: Properly merge possibly duplicate scalac options
        val allScalacOptions = additionalScalacOptions ++ currentCompileInputs.options.scalacOptions
        val newOptions = currentCompileInputs.options.withScalacOptions(allScalacOptions.toArray)
        currentCompileInputs.withOptions(newOptions)
      }
    )
  }

  private def reportBugText: String = s"This is a bug on sbt-stainless, please report it: $IssueTracker"
}
