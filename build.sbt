import java.io.{BufferedReader, FileReader}

scalaVersion in ThisBuild := "2.12.8"

//scalacOptions in ThisBuild ++= Seq("-Xno-patmat-analysis")

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

lazy val macros = (project in file("keymaerax-macros"))

lazy val keymaeraxCoreAssemblySettings = AssemblyPlugin.assemblySettings ++ Seq(
  test in assembly := {},
  mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX"),
  assemblyJarName in assembly := s"keymaerax-core-${version.value}.jar",
  assemblyMergeStrategy in assembly := {
    case PathList("examples", xs @ _*) => MergeStrategy.last
    case x                             => (assemblyMergeStrategy in assembly).value(x)
  })

// build KeYmaera X core jar with sbt "project core" clean assembly
lazy val core = (project in file("keymaerax-core"))
  .dependsOn(macros)
  .settings(
    name := "KeYmaeraX Core",
    assemblyJarName := "keymaerax-core-" + version.value + ".jar",
    scalacOptions in (ScalaUnidoc, unidoc) += "-Ymacro-expand:none"
  )
  .settings(keymaeraxCoreAssemblySettings: _*)
  .aggregate(macros)

lazy val keymaeraxFullAssemblySettings = AssemblyPlugin.assemblySettings ++
  Seq(test in assembly := {},
    mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.Main"),
    assemblyJarName in assembly := "keymaerax.jar",
    assemblyMergeStrategy in assembly := {
      case PathList("examples", xs @ _*) => MergeStrategy.last
      case x                             => (assemblyMergeStrategy in assembly).value(x)
    })

lazy val keymaerax = (project in file("keymaerax-webui"))
  .dependsOn(macros, core)
  .settings(inConfig(Test)(keymaeraxFullAssemblySettings): _*)

// build KeYmaera X full jar with sbt clean assembly
lazy val root = (project in file("."))
  .enablePlugins(ScalaUnidocPlugin)
  .settings(
    name := "KeYmaeraX",
    assemblyJarName := "keymaerax-" + version.value + ".jar",
    scalacOptions in (ScalaUnidoc, unidoc) += "-Ymacro-expand:none",
    ScalaUnidoc / unidoc / unidocProjectFilter := inAnyProject -- inProjects(macros)
  )
  .settings(keymaeraxFullAssemblySettings: _*)
  .aggregate(macros, core, keymaerax)


// extra runtime checks for initialization order: "-Xcheckinit"
scalacOptions in Compile ++= Seq("-doc-root-content", "rootdoc.txt")
scalacOptions in Compile += "-Ystatistics:typer"

target in Compile in doc := baseDirectory.value / "api"

// never execute tests in parallel across all sub-projects
concurrentRestrictions in Global += Tags.limit(Tags.Test, 1)
