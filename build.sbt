import java.io.{BufferedReader, FileInputStream, FileReader, InputStreamReader}
import java.nio.charset.StandardCharsets
import java.util.Properties

ThisBuild / scalaVersion := "2.12.8"
ThisBuild / version := {
  // TODO Make this build file the single source of truth for version number
  // and remove or autogenerate the VERSION file in the process
  new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()
}

lazy val macros = project
  .in(file("keymaerax-macros"))
  .disablePlugins(AssemblyPlugin)
  .settings(
    name := "KeYmaeraX Macros",

    libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.12.8",
    libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.12.8",

    resolvers ++= Resolver.sonatypeOssRepos("releases"),
    addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full),

    Compile / doc / scalacOptions ++= Seq("-doc-root-content", "rootdoc.txt"),
  )

lazy val core = project
  .in(file("keymaerax-core"))
  .dependsOn(macros)
  .settings(
    name := "KeYmaeraX Core",

    libraryDependencies += "biz.enef" %% "slogging-slf4j" % "0.6.+",
    libraryDependencies += "cc.redberry" %% "rings.scaladsl" % "2.5.2",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.2.2",
    libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.2",
    libraryDependencies += "io.spray" %% "spray-json" % "1.3.4",
    libraryDependencies += "org.apache.commons" % "commons-configuration2" % "2.5",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-slf4j-impl" % "2.17.1",
    libraryDependencies += "org.reflections" % "reflections" % "0.10.2",
    libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.12.8",
    libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.12.8",
    libraryDependencies += "org.typelevel" %% "paiges-core" % "0.2.1",
    libraryDependencies += "org.typelevel" %% "spire" % "0.16.2",

    resolvers ++= Resolver.sonatypeOssRepos("releases"),
    addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full),

    Compile / doc / scalacOptions ++= Seq("-doc-root-content", "rootdoc.txt"),
    ScalaUnidoc / unidoc / scalacOptions += "-Ymacro-expand:none",

    assembly / mainClass := Some("edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX"),
    assembly / assemblyJarName := s"${normalizedName.value}-${version.value}.jar",
    assembly / test := {},

    // Use Mathematica's JLink.jar as unmanaged dependency
    // The path is read from the property mathematica.jlink.path in the file local.properties
    Compile / unmanagedJars += {
      val properties = new Properties()
      try {
        val stream = new FileInputStream("local.properties")
        val reader = new InputStreamReader(stream, StandardCharsets.UTF_8)
        properties.load(reader)
      } catch {
        case e: Throwable => throw new Exception("Failed to load file local.properties", e)
      }
      val jlinkPath: String = properties.getProperty("mathematica.jlink.path")
      if (jlinkPath == null) {
        throw new Exception("Property mathematica.jlink.path not found in file local.properties")
      }
      file(jlinkPath)
    },
  )

lazy val keymaeraxFullAssemblySettings = AssemblyPlugin.assemblySettings ++
  Seq(
    assembly / test := {},
    assembly / mainClass := Some("edu.cmu.cs.ls.keymaerax.launcher.Main"),
    assembly / assemblyJarName := "keymaerax.jar",
    assembly / assemblyMergeStrategy := {
      case PathList("examples", xs @ _*) => MergeStrategy.last
      case x => (assembly / assemblyMergeStrategy).value(x)
    },
  )

lazy val keymaerax = (project in file("keymaerax-webui"))
  .dependsOn(macros, core)
  .settings(inConfig(Test)(keymaeraxFullAssemblySettings): _*)

// build KeYmaera X full jar with sbt clean assembly
lazy val root = (project in file("."))
  .enablePlugins(ScalaUnidocPlugin)
  .settings(
    name := "KeYmaeraX",
    assemblyJarName := "keymaerax-" + version.value + ".jar",
    ScalaUnidoc / unidoc / scalacOptions += "-Ymacro-expand:none",
    ScalaUnidoc / unidoc / unidocProjectFilter := inAnyProject -- inProjects(macros),
  )
  .settings(keymaeraxFullAssemblySettings: _*)
  .aggregate(macros, core, keymaerax)


// extra runtime checks for initialization order: "-Xcheckinit"
Compile / scalacOptions += "-Ystatistics:typer"

Compile / doc / target := baseDirectory.value / "api"
Compile / doc / scalacOptions ++= Seq("-doc-root-content", "rootdoc.txt")

// never execute tests in parallel across all sub-projects
Global / concurrentRestrictions += Tags.limit(Tags.Test, 1)
