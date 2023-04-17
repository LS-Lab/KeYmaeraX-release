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
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "MapConfiguration.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "Logging.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "Assertion.java",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "Version.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "package.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "Expression.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "PrettyPrinter.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "Sequent.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "SetLattice.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "StaticSemantics.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "UniformSubstitution.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "core" / "USubstOne.scala",
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
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "InterpretedSymbols.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "BuiltinSymbols.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "ReservedSymbols.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "TacticReservedSymbols.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "Location.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "InterpretedSymbols.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "OpSpec.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "ODEToInterpreted.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "SequentParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "PrettyPrinter.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "Stack.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "Parser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXPrettyPrinter.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXTerminals.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "DLParserUtils.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "DLParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "SubstitutionParser.scala",

    // for archive and tactic parsing
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-macros" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "btactics" / "macros" / "ArgInfo.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "bellerophon" / "PositionLocator.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "bellerophon" / "parser" / "TacticParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "bellerophon" / "BelleLabel.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "bellerophon" / "parser" / "DLBelleParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "ArchiveParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "DLArchiveParser.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "FormatProvider.scala",
    unmanagedSources in Compile +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "edu" / "cmu" / "cs" / "ls" / "keymaerax" / "parser" / "KeYmaeraXArchivePrinter.scala"
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
