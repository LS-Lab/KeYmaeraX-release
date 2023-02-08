import java.io.{BufferedReader, FileInputStream, FileReader}
import java.util.Properties

name := "KeYmaeraX-Core"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

assemblyJarName in assembly := s"keymaerax-core-${version.value}.jar"

scalaVersion := "2.12.8"

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.12.8"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.12.8"

libraryDependencies += "biz.enef" %% "slogging-slf4j" % "0.6.+"

libraryDependencies += "org.apache.logging.log4j" % "log4j-slf4j-impl" % "2.17.1"

libraryDependencies += "org.apache.commons" % "commons-configuration2" % "2.5"

libraryDependencies += "org.typelevel" %% "paiges-core" % "0.2.1"

libraryDependencies += "org.typelevel" %% "spire" % "0.16.2"

libraryDependencies += "io.spray" %% "spray-json" % "1.3.4"

libraryDependencies += "cc.redberry" %% "rings.scaladsl" % "2.5.2"

libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.2.2"

libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.2"

libraryDependencies += "org.reflections" % "reflections" % "0.10.2"

resolvers += Resolver.sonatypeRepo("releases")
addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full)

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
