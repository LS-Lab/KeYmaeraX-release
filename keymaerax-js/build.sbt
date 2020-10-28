name := "KeYmaeraX-JS"

scalaVersion in ThisBuild := "2.12.8"

enablePlugins(ScalaJSPlugin)

scalaJSUseMainModuleInitializer := false

// select core sources to include
lazy val root = (project in file("."))
  .settings(
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "Configuration.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "Logging.scala",
    unmanagedSources in Compile ++=
      coreSources(baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core"),
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "Position.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "Location.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "OpSpec.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "ParserErrors.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "PrettyPrinter.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "Stack.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "Parser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXPrettyPrinter.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXLexer.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXStoredProvableParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXAxiomParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "DLParser.scala"
  )

scalacOptions in Compile ++= Seq(
    "-optimise",
    "-Xelide-below", "10000",
    "-Xdisable-assertions")

libraryDependencies += "biz.enef" %%% "slogging" % "0.6.+"

libraryDependencies += "com.lihaoyi" %%% "fastparse" % "2.2.+"

def coreSources(dir: File): Vector[File] = {
  (dir * "*.scala").get.toVector ++ (dir * "*.java").get.toVector
}