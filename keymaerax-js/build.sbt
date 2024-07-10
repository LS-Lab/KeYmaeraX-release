name := "KeYmaeraX-JS"

ThisBuild / scalaVersion := "2.13.12"

enablePlugins(ScalaJSPlugin)

scalaJSUseMainModuleInitializer := false

// select core sources to include
lazy val root = project
  .in(file("."))
  .settings(
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "Configuration.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "MapConfiguration.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "Logging.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "Assertion.java",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "Version.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "package.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "Expression.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "PrettyPrinter.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "Sequent.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "SetLattice.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "StaticSemantics.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "UniformSubstitution.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "core" / "USubstOne.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "Position.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "FormulaTools.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "ExpressionTraversal.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "Augmentors.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "Context.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "SubstitutionHelper.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "DependencyAnalysis.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "infrastruct" / "StaticSemanticsTools.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "InterpretedSymbols.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "BuiltinSymbols.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "ReservedSymbols.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "TacticReservedSymbols.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "Location.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "InterpretedSymbols.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "OpSpec.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "ODEToInterpreted.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "SequentParser.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "PrettyPrinter.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "Stack.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "Parser.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "KeYmaeraXPrettyPrinter.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "KeYmaeraXTerminals.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "DLParserUtils.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "DLParser.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "SubstitutionParser.scala",

    // for archive and tactic parsing
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-macros" / "src" / "main" / "scala" / "org" / "keymaerax" / "btactics" / "macros" / "ArgInfo.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "bellerophon" / "PositionLocator.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "bellerophon" / "parser" / "TacticParser.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "bellerophon" / "BelleLabel.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "bellerophon" / "parser" / "DLBelleParser.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "ArchiveParser.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "DLArchiveParser.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "FormatProvider.scala",
    Compile / unmanagedSources +=
      baseDirectory.value.getParentFile / "keymaerax-core" / "src" / "main" / "scala" / "org" / "keymaerax" / "parser" / "KeYmaeraXArchivePrinter.scala"
  )

Compile / scalacOptions ++= Seq(
    "-optimise",
    "-Xelide-below", "10000",
    "-Xdisable-assertions")

libraryDependencies += "biz.enef" %%% "slogging" % "0.6.+"

libraryDependencies += "com.lihaoyi" %%% "fastparse" % "3.0.2"

def coreSources(dir: File): Vector[File] = {
  (dir * "*.scala").get.toVector ++ (dir * "*.java").get.toVector
}
