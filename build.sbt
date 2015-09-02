scalaVersion := "2.10.4"                                                        

val versionName : String = "4.0a4"

version := versionName

lazy val core = (project in file("keymaerax-core"))

lazy val keymaerax = (project in file("keymaerax-webui")).
  dependsOn(core)

lazy val root = (project in file("."))
  .settings(unidocSettings: _*)
  .settings(
    name := "KeYmaeraX",
    assemblyJarName := "keymaerax-" + versionName + ".jar"
  )
  .aggregate(core, keymaerax)
