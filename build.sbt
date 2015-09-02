<<<<<<< HEAD
scalaVersion in ThisBuild := "2.11.7"

scalacOptions in ThisBuild ++= Seq("-Xno-patmat-analysis")

version := "4.0a4"
=======
scalaVersion := "2.11.6"                                                        
>>>>>>> 9ae193e697f32c56ab1fcf3e8b9c0750ec8c0ae1

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
