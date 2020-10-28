import java.io.FileInputStream
import java.util.Properties

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

////////////////////////////////////////////////////////////////////////////////
// Mathematica Interop
////////////////////////////////////////////////////////////////////////////////
//{
//  def read(fileName: String): Option[Properties] = {
//    try {
//      val prop = new Properties()
//      prop.load(new FileInputStream(fileName))
//      Some(prop)
//    } catch {
//      case e: Throwable =>
//        println("local.properties not found: please copy default.properties and adapt the paths to your system")
//        None
//    }
//  }
//  val properties: Properties = read("../local.properties").orElse(read("../default.properties")).get
//  val jlinkJarLoc: String = properties.getProperty("mathematica.jlink.path")
//  if (jlinkJarLoc == null) throw new Exception("Need 'mathematica.jlink.path' set to location of the Mathematica JLink.jar file in 'local.properties' before building project.")
//  unmanagedJars in Compile += file(jlinkJarLoc)
//}

def coreSources(dir: File): Vector[File] = {
  (dir * "*.scala").get.toVector ++ (dir * "*.java").get.toVector
}