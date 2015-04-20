lazy val core = (project in file("core"))

lazy val KeYmaeraX = (project in file("fullProver")).
  dependsOn(core)

lazy val root = (project in file("."))
  .aggregate(core, KeYmaeraX)


