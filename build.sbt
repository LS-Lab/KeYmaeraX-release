scalaVersion in ThisBuild := "2.11.7"

//scalacOptions in ThisBuild ++= Seq("-Xno-patmat-analysis")

version := "4.0b1"

lazy val core = (project in file("keymaerax-core"))

lazy val keymaerax = (project in file("keymaerax-webui")).
  dependsOn(core)

lazy val root = (project in file("."))
  .settings(unidocSettings: _*)
  .settings(
    name := "KeYmaeraX",
    assemblyJarName := "keymaerax-" + version.value + ".jar"
  )
  .aggregate(core, keymaerax)


scalacOptions in Compile ++= Seq("-doc-root-content", "rootdoc.txt")

target in Compile in doc := baseDirectory.value / "api"
