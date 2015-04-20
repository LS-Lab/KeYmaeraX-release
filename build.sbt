lazy val core = (project in file("keymaerax-core"))

lazy val KeYmaeraX = (project in file("keymaerax-webui")).
  dependsOn(core)

lazy val root = (project in file("."))
  .aggregate(core, KeYmaeraX)

