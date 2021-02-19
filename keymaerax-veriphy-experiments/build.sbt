import java.io.{BufferedReader, FileInputStream, FileReader}
import java.util.Properties

name := "KeYmaeraX-VeriPhy-Experiments"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots" // ScalaMeter

assemblyJarName in (Test, assembly) := s"keymaerax-veriphy-experiments${version.value}.jar"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

libraryDependencies += "net.java.dev.jna" % "jna" % "5.6.0"

libraryDependencies += "biz.enef" %%% "slogging" % "0.6.+"

//libraryDependencies += "com.jsuereth" %% "scala-arm" % "2.0" // automatic resource management

//libraryDependencies += "org.apache.logging.log4j" % "log4j-slf4j-impl" % "2.13.3"

//libraryDependencies += "org.apache.commons" % "commons-configuration2" % "2.5"

//libraryDependencies += "cc.redberry" %% "rings.scaladsl" % "2.5.2"

libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.2.2"

//libraryDependencies += "org.typelevel" %% "spire" % "0.16.2"


resolvers += "Typesafe Repo" at "http://repo.typesafe.com/typesafe/releases/" // contains json-schema-validtor.

scalacOptions := Seq( "-encoding", "utf8") // "-unchecked", "-deprecation",

javaOptions += "-Xss20M"


logBuffered := false

////////////////////////////////////////////////////////////////////////////////
// Builds -- make sure you are using SBT 13.6+
////////////////////////////////////////////////////////////////////////////////

scalaJSUseMainModuleInitializer := false



lazy val keymaeraxExperimentsAssemblySettings = AssemblyPlugin.assemblySettings ++
  Seq(test in assembly := {},
      mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.veriphy.experiments.BotMain"),
      assemblyJarName in assembly := "veriphy-experiment.jar",
      assemblyMergeStrategy in assembly := {
          case PathList("examples", xs @ _*) => MergeStrategy.last
          case x                             => (assemblyMergeStrategy in assembly).value(x)
      })
// select core sources to include
//lazy val root = (project in file("."))
//    .settings(scalacOptions := Seq( "-encoding", "utf8"))
//    .settings((keymaeraxExperimentsAssemblySettings): _*)  /*inConfig(Test)*/
  /*
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

  )*/


scalacOptions in Compile ++= Seq(
  "-optimise",
  "-Xelide-below", "10000",
  "-Xdisable-assertions")


def coreSources(dir: File): Vector[File] = {
  (dir * "*.scala").get.toVector ++ (dir * "*.java").get.toVector
}

// command line UI
mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.veriphy.experiments.BotMain")

// do not run tests when building assembly
test in assembly :=  {}

