scalaVersion := "2.10.4"                                                        

lazy val core = (project in file("keymaerax-core"))

lazy val keymaerax = (project in file("keymaerax-webui")).
  dependsOn(core)

lazy val root = (project in file("."))
  .settings(unidocSettings: _*)
  .settings(
    name := "KeYmaeraX",
  )
  .aggregate(core, keymaerax)
