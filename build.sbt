import java.io.{BufferedReader, FileReader}

scalaVersion in ThisBuild := "2.12.8"

//scalacOptions in ThisBuild ++= Seq("-Xno-patmat-analysis")

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

lazy val macros = (project in file("keymaerax-macros"))

/*lazy val keymaeraxCoreAssemblySettings = AssemblyPlugin.assemblySettings ++ Seq(
  test in assembly := {},
  mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX"),
  assemblyJarName in assembly := s"keymaerax-core-${version.value}.jar",
  assemblyMergeStrategy in assembly := {
    case PathList("examples", xs @ _*) => MergeStrategy.last
    case x                             => (assemblyMergeStrategy in assembly).value(x)
  })*/

// build KeYmaera X core jar with sbt "project core" clean assembly
lazy val core = (project in file("keymaerax-core"))
  .dependsOn(macros)
  /*.settings(
    name := "KeYmaeraX Core",
    assemblyJarName := "keymaerax-core-" + version.value + ".jar",
    scalacOptions in (ScalaUnidoc, unidoc) += "-Ymacro-expand:none"
  )*/
  //.settings(keymaeraxCoreAssemblySettings: _*)
  //.aggregate(macros)


lazy val experiments = (project in file("keymaerax-veriphy-experiments"))
  /*.dependsOn(core)*/
  .settings(
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "Configuration.scala",
    //unmanagedSources in Compile +=
    //  baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "FileConfiguration.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "Logging.scala",
    unmanagedSources in Compile ++=
      coreSources(baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core"),
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "Position.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "FormulaTools.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "ExpressionTraversal.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "Augmentors.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "Context.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "SubstitutionHelper.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "DependencyAnalysis.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "StaticSemanticsTools.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "Location.scala",
    //unmanagedSources in Compile +=
    //baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "StringConverter.scala",
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
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "DLParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "SubstitutionParser.scala",

    /*unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "UnificationMatch.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "UnificationMatchImpl.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "MultiRename.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "infrastruct" / "RenUSubst.scala",*/
    // for archive and tactic parsing
    //    unmanagedSources in Compile +=
    //      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "bellerophon" / "parser" / "TacticParser.scala",
    //    unmanagedSources in Compile +=
    //      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "bellerophon" / "parser" / "DLBelleParser.scala",
    //unmanagedSources in Compile +=
    //  baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "ArchiveParser.scala",
    //    unmanagedSources in Compile +=
    //      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "DLArchiveParser.scala",
    //    unmanagedSources in Compile +=
    //      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXArchivePrinter.scala",
    //    unmanagedSources in Compile +=
    //
    //        baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXArchiveParserBase.scala"

  )
  //.dependsOn(macros, core)

def coreSources(dir: File): Vector[File] = {
    (dir * "*.scala").get.toVector ++ (dir * "*.java").get.toVector
}

lazy val keymaeraxFullAssemblySettings = AssemblyPlugin.assemblySettings ++
  Seq(test in assembly := {},
      mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.Main"),
      assemblyJarName in assembly := "keymaerax.jar",
      assemblyMergeStrategy in assembly := {
          case PathList("examples", xs @ _*) => MergeStrategy.last
          case x                             => (assemblyMergeStrategy in assembly).value(x)
      })

/*lazy val keymaeraxKaisarAssemblySettings = AssemblyPlugin.assemblySettings ++
  Seq(test in assembly := {},
    mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.cdgl.kaisar.StrategyExtractorMain"),
    assemblyJarName in assembly := "kaisar-strategy.jar",
    assemblyMergeStrategy in assembly := {
      case PathList("examples", xs @ _*) => MergeStrategy.last
      case x                             => (assemblyMergeStrategy in assembly).value(x)
    })*/

lazy val keymaerax = (project in file("keymaerax-webui"))
  .dependsOn(macros, core)
  .settings(inConfig(Test)(keymaeraxFullAssemblySettings): _*)

lazy val keymaeraxExperimentsAssemblySettings = AssemblyPlugin.assemblySettings ++
  Seq(test in assembly := {},
      mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.veriphy.experiments.AirBotMain"),
      assemblyJarName in assembly := "veriphy-experiment.jar",
      assemblyMergeStrategy in assembly := {
          case PathList("examples", xs @ _*) => MergeStrategy.last
          case x                             => (assemblyMergeStrategy in assembly).value(x)
      })
// build KeYmaera X full jar with sbt clean assembly
lazy val root = experiments
  .settings((keymaeraxExperimentsAssemblySettings): _*)  /*inConfig(Test)*/

  /*.enablePlugins(ScalaUnidocPlugin)
  .settings(
    name := "KeYmaeraX",
    assemblyJarName := "keymaerax-" + version.value + ".jar",
    scalacOptions in (ScalaUnidoc, unidoc) += "-Ymacro-expand:none"
  )
  .settings(keymaeraxFullAssemblySettings: _*)
  .aggregate(macros, core, keymaerax, experiments)*/


// extra runtime checks for initialization order: "-Xcheckinit"
scalacOptions in Compile ++= Seq("-doc-root-content", "rootdoc.txt")
scalacOptions in Compile += "-Ystatistics:typer"

target in Compile in doc := baseDirectory.value / "api"

// never execute tests in parallel across all sub-projects
concurrentRestrictions in Global += Tags.limit(Tags.Test, 1)
