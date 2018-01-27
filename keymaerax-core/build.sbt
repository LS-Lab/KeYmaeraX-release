import java.io.{BufferedReader, FileInputStream, FileReader}
import java.util.Properties

name := "KeYmaeraX-Core"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

assemblyJarName in assembly := s"keymaerax-core-${version.value}.jar"

scalaVersion := "2.11.7"

//scalacOptions ++= Seq("-Xno-patmat-analysis")

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.7"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.11.7"

libraryDependencies += "org.apache.commons" % "commons-configuration2" % "2.2"

libraryDependencies += "org.apache.logging.log4j" % "log4j-api" % "2.10.0"

libraryDependencies += "org.apache.logging.log4j" % "log4j-core" % "2.10.0"

libraryDependencies += "org.apache.logging.log4j" %% "log4j-api-scala" % "11.0"

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
        println("local.properties not found: please copy default.properties and adapt the paths to your system")
        None
    }
  }
  val properties: Properties = read("local.properties").orElse(read("default.properties")).get
  val jlinkJarLoc: String = properties.getProperty("mathematica.jlink.path")
  if (jlinkJarLoc == null) throw new Exception("Need 'mathematica.jlink.path' set to location of the Mathematica JLink.jar file in 'local.properties' before building project.")
  unmanagedJars in Compile += file(jlinkJarLoc)
}
