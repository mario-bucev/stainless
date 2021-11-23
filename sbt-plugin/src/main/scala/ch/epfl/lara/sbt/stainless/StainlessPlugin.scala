package ch.epfl.lara.sbt.stainless

import sbt.Keys._
import sbt._

import java.io.File
import java.net.{URL, URLClassLoader}
import java.nio.file._
import java.util.Comparator
import java.util.stream.Collectors
import java.util.zip.{ZipEntry, ZipFile}
import scala.jdk.CollectionConverters._

object StainlessPlugin extends sbt.AutoPlugin {
  private val IssueTracker = "https://github.com/epfl-lara/stainless/issues"
  // The Scala version with which Stainless is compiled.
  private val stainlessScalaVersion = BuildInfo.stainlessScalaVersion
  // e.g. for 2.13.6, this would yield 2.13
  private val stainlessLibScalaBinaryVersion = CrossVersion.binaryScalaVersion(BuildInfo.stainlessLibScalaVersion)

  override def requires: Plugins = plugins.JvmPlugin
  override def trigger: PluginTrigger = noTrigger // This plugin needs to be manually enabled

  object autoImport {
    lazy val stainlessVersion        = settingKey[String]("The version of stainless to use")
    lazy val stainlessEnabled        = settingKey[Boolean]("Enable stainless")
    lazy val stainlessExtraDeps      = settingKey[Seq[sbt.librarymanagement.ModuleID]]("Extra source dependencies to pass along to Stainless")
    lazy val stainlessExtraResolvers = settingKey[Seq[sbt.librarymanagement.MavenRepository]]("Extra resolvers to pass along to Stainless")
    lazy val verify                  = taskKey[Unit]("Proceed to verification")
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
    verify                  := verifyTask.value,
    clean                   := cleanTask.value,

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
    val pluginRef = {
      // Note: the version of stainless-dotty/scalac-plugin to use depends on the Scala version
      // Stainless was compiled with, not the user project Scala version.
      // For instance, if Stainless was compiled with 3.0.2 and the user uses Scala 2.13.6,
      // we would fetch stainless-scalac-plugin_3.0.2 (and not stainless-scalac-plugin_2.13.6)
      if (isScala3.value)
        "ch.epfl.lara" % s"stainless-dotty-plugin_$stainlessScalaVersion" % stainlessVersion.value
      else
        "ch.epfl.lara" % s"stainless-scalac-plugin_$stainlessScalaVersion" % stainlessVersion.value
    }
    val libraryRef = "ch.epfl.lara" % s"stainless-library_$stainlessLibScalaBinaryVersion" % stainlessVersion.value
    val sourceDeps = (libraryRef +: stainlessExtraDeps.value).map { dep =>
      dep.intransitive().sources() % StainlessLibSources
    }
    compilerPlugin(pluginRef) +: sourceDeps :+ "ch.epfl.lara" % "stainless-library_2.13" % "0.9.1-59-g8e80911-SNAPSHOT-compiled"
  }

  lazy val stainlessConfigSettings: Seq[Def.Setting[_]] =
    Seq(
      managedSources ++= fetchAndUnzipSourceDeps.value,
      managedSourceDirectories += stainlessSourcesLocation.value
    )

  private def stainlessSourcesLocation = Def.setting {
    target.value / s"stainless_$stainlessLibScalaBinaryVersion"
  }

  private def stainlessBinFolder = Def.setting {
    crossTarget.value / "stainless"
  }

  private def isScala3 = Def.setting {
    scalaVersion.value.startsWith("3.")
  }

  private def verifyTask: Def.Initialize[Task[Unit]] = Def.task {
    val prevCompileRes = (Compile / previousCompile).value
    // Note: if compilation fails, the task is terminated.
    val compileRes = (Compile / compile).value

    val converter = fileConverter.value
    val log = streams.value.log
    val upd = update.value
    val compilerOpts = (Compile / scalacOptions).value
    val scalaSrcFolder = (Compile / scalaSource).value
    val binFolder = stainlessBinFolder.value

    // For the Scalac frontend, the verification is always embedded in the compilation phase.
    // For the Dotty frontend, the verification is also embedded if the users passes -P:stainless:inc-comp:false
    // Otherwise, the verification and compilation are separated, and we must proceed to invoke the verify method of StainlessVerification.
    if (isScala3.value && !disableIncrementalCompilation(compilerOpts)) {
      val prevCompiledSources = prevCompileRes.analysis().asScala.map(_.readSourceInfos().getAllSourceInfos.keySet().asScala.toSet)
      val compiledSources = compileRes.readSourceInfos().getAllSourceInfos.keySet().asScala.toSet
      val removedFiles0 = prevCompiledSources.map(_ -- compiledSources).getOrElse(Set.empty)
      val removedFiles = removedFiles0.map(vf => converter.toPath(vf).toFile)

      val stainlessBinsToRemove = removedFiles.map { rm =>
        val relative = rm.getAbsolutePath.drop(scalaSrcFolder.getAbsolutePath.length + 1) // The + 1 is to also remove the trailing /
        new File(binFolder, relative.replace(".scala", ".bin"))
      }
      log.debug {
        val base = baseDirectory.value
        val relative = stainlessBinsToRemove.map(f => f.getAbsolutePath.drop(base.getAbsolutePath.length + 1))
        s"""Stainless .bin files to be removed: ${relative.mkString(",")}"""
      }
      stainlessBinsToRemove.foreach(_.delete())

      val stainlessDottyPluginJar = Classpaths.autoPlugins(upd, Seq.empty, true).head.drop("-Xplugin:".length)
      val classLoader = new WackyClassLoader(Array(new File(stainlessDottyPluginJar).toURI.toURL))
      val stainlessVerifClass = Class.forName("stainless.frontends.dotc.sbt.StainlessVerification", false, classLoader)
      val stainlessVerifInstance = stainlessVerifClass.newInstance()
      val verifyMeth = stainlessVerifClass.getMethod("verify", classOf[java.io.File])
      verifyMeth.invoke(stainlessVerifInstance, binFolder)
    }
  }

  private def cleanTask: Def.Initialize[Task[Unit]] = Def.task {
    (Compile / clean).value
    // https://www.baeldung.com/java-delete-directory#conclusion-1
    Files.walk(stainlessBinFolder.value.toPath)
      .sorted(Comparator.reverseOrder())
      .forEach(Files.delete)
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
        val additionalScalacOptions =
          // skipping the sbt incremental compiler phases because the interact badly with stainless (especially, a NPE
          // is thrown while executing the xsbt-dependency phase because it attempts to time-travels symbol to compiler phases
          // that are run *after* the stainless phase.
          (if (!isScala3.value)
            Seq("-Yskip:xsbt-dependency,xsbt-api,xsbt-analyzer")
          else if (disableIncrementalCompilation(currentCompileInputs.options().scalacOptions()))
            // Disable incremental compilation performed by SBT as well.
            Seq("-Yskip:sbt-deps,sbt-api")
          else Seq.empty) ++
          Seq(
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

  private def disableIncrementalCompilation(args: Seq[String]): Boolean =
    args.contains("-P:stainless:inc-comp:false")

  private def reportBugText: String = s"This is a bug on sbt-stainless, please report it: $IssueTracker"

  // TODO: Explain
  private class WackyClassLoader(urls: Array[URL]) extends URLClassLoader(urls) {
    override def loadClass(name: String, resolve: Boolean): Class[_] = {
      getClassLoadingLock(name).synchronized {
        if (name.startsWith("scala")) {
          val x = super.findLoadedClass(name)
          if (x == null) super.findClass(name)
          else x
        }
        else super.loadClass(name, resolve)
      }
    }
  }
}
