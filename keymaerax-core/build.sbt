import java.io.{BufferedReader, FileInputStream, FileReader}
import java.util.Properties

name := "KeYmaeraX-Core"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

assemblyJarName in assembly := "keymaerax-core.jar" 

scalaVersion := "2.11.7"

//scalacOptions ++= Seq("-Xno-patmat-analysis")

resolvers += "Apache Commons IO" at "https://mvnrepository.com/artifact/commons-io/commons-io"

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.7"

libraryDependencies += "commons-io" % "commons-io" % "2.5" // BOMInputStream to read files that browsers store (CourseMain)

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

