scalaVersion in ThisBuild := "2.11.7"

//scalacOptions in ThisBuild ++= Seq("-Xno-patmat-analysis")

version := "4.0b1"

lazy val core = (project in file("keymaerax-core"))

lazy val keymaeraxAssemblySettings = AssemblyPlugin.assemblySettings ++ Seq(
  mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX"),
  assemblyJarName in assembly := "keymaerax-web-" + version.value + ".jar",
  test in assembly := {},
  assemblyMergeStrategy in assembly := {
    case PathList("examples", xs @ _*) => MergeStrategy.last
    case x                             => (assemblyMergeStrategy in assembly).value(x)
  }
)

lazy val keymaerax = (project in file("keymaerax-webui"))
  .dependsOn(core)
  .settings(inConfig(Test)(keymaeraxAssemblySettings): _*)

lazy val root = (project in file("."))
  .settings(unidocSettings: _*)
  .settings(
    name := "KeYmaeraX",
    assemblyJarName := "keymaerax-" + version.value + ".jar"
  )
  .settings(inConfig(Test)(keymaeraxAssemblySettings): _*)
  .aggregate(core, keymaerax)


scalacOptions in Compile ++= Seq("-doc-root-content", "rootdoc.txt")

target in Compile in doc := baseDirectory.value / "api"
