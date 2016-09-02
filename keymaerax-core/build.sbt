import java.io.{BufferedReader, FileInputStream, FileReader}
import java.util.Properties

name := "KeYmaeraX-Core"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

assemblyJarName in assembly := "keymaerax-core.jar" 

scalaVersion := "2.11.7"

//scalacOptions ++= Seq("-Xno-patmat-analysis")

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.7"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

