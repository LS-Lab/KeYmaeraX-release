scalaVersion in ThisBuild := "2.11.7"

scalacOptions in ThisBuild ++= Seq("-Xno-patmat-analysis")

version := "4.0a4"

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
