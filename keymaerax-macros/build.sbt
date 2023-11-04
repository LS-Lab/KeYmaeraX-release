import java.io.{BufferedReader, FileInputStream, FileReader}
import java.util.Properties

name := "KeYmaeraX-Macros"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

assembly / assemblyJarName := s"keymaerax-macros-${version.value}.jar"

scalaVersion := "2.12.8"

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.12.8"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.12.8"

resolvers ++= Resolver.sonatypeOssRepos("releases")
addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full)

Compile / doc / scalacOptions ++= Seq("-doc-root-content", "rootdoc.txt")
