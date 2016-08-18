import java.io.FileInputStream
import java.util.Properties

name := "KeYmaeraX-Core"

assemblyJarName in assembly := "keymaerax-core.jar" 

scalaVersion := "2.11.7"

//scalacOptions ++= Seq("-Xno-patmat-analysis")

//parser combinators are not longer included by default.
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4"

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.7"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

////////////////////////////////////////////////////////////////////////////////
// Mathematica Interop
////////////////////////////////////////////////////////////////////////////////
{
  def read(fileName: String): Option[Properties] = {
    try {
      val prop = new Properties()
      prop.load(new FileInputStream(fileName))
      Some(prop)
    } catch {
      case e: Throwable =>
        e.printStackTrace()
        None
    }
  }
  val properties: Properties = read("local.properties").orElse(read("default.properties")).get
  val jlinkJarLoc: String = properties.getProperty("mathematica.jlink.path")
  if (jlinkJarLoc == null) throw new Exception("Need 'mathematica.jlink.path' set to location of the Mathematica JLink.jar file in 'local.properties' before building project.")
  unmanagedJars in Compile += file(jlinkJarLoc)
}
