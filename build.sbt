import java.io.{BufferedReader, FileReader}

scalaVersion in ThisBuild := "2.12.8"

//scalacOptions in ThisBuild ++= Seq("-Xno-patmat-analysis")

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

lazy val macros = (project in file("keymaerax-macros"))

lazy val core = (project in file("keymaerax-core"))
  .dependsOn(macros)

lazy val keymaeraxAssemblySettings = AssemblyPlugin.assemblySettings ++ Seq(
  mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.Main"),
  assemblyJarName in assembly := "keymaerax.jar",
  test in assembly := {},
  assemblyMergeStrategy in assembly := {
    case PathList("examples", xs @ _*) => MergeStrategy.last
    case x                             => (assemblyMergeStrategy in assembly).value(x)
  }
)

lazy val keymaerax = (project in file("keymaerax-webui"))
  .dependsOn(macros, core)
  .settings(inConfig(Test)(keymaeraxAssemblySettings): _*)


lazy val root = (project in file("."))
  .enablePlugins(ScalaUnidocPlugin)
  .settings(
    name := "KeYmaeraX",
    assemblyJarName := "keymaerax-" + version.value + ".jar",
    scalacOptions in (ScalaUnidoc, unidoc) += "-Ymacro-expand:none"
  )
  .settings(inConfig(Test)(keymaeraxAssemblySettings): _*)
  .aggregate(macros, core, keymaerax)


// extra runtime checks for initialization order: "-Xcheckinit"
scalacOptions in Compile ++= Seq("-doc-root-content", "rootdoc.txt")
scalacOptions in Compile += "-Ystatistics:typer"

target in Compile in doc := baseDirectory.value / "api"

// never execute tests in parallel across all sub-projects
concurrentRestrictions in Global += Tags.limit(Tags.Test, 1)
