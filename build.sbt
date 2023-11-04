import java.io.{BufferedReader, FileReader}

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

lazy val keymaeraxCoreAssemblySettings = AssemblyPlugin.assemblySettings ++ Seq(
  assembly / test := {},
  assembly / mainClass := Some("edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX"),
  assembly / assemblyJarName := s"keymaerax-core-${version.value}.jar",
  assembly / assemblyMergeStrategy := {
    case PathList("examples", xs @ _*) => MergeStrategy.last
    case x => (assembly / assemblyMergeStrategy).value(x)
  })

// build KeYmaera X core jar with sbt "project core" clean assembly
lazy val core = (project in file("keymaerax-core"))
  .dependsOn(macros)
  .settings(
    name := "KeYmaeraX Core",
    assemblyJarName := "keymaerax-core-" + version.value + ".jar",
    ScalaUnidoc / unidoc / scalacOptions += "-Ymacro-expand:none",
  )
  .settings(keymaeraxCoreAssemblySettings: _*)
  .aggregate(macros)

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
