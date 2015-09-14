name := "KeYmaeraX-Core"

version := "4.0a4"

assemblyJarName in assembly := "keymaerax-core-" + version.value + ".jar" 

scalaVersion := "2.11.7"

//scalacOptions ++= Seq("-Xno-patmat-analysis")

//parser combinators are not longer included by default.
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

////////////////////////////////////////////////////////////////////////////////
// Mathematica Interop
////////////////////////////////////////////////////////////////////////////////
{
  val jlinkJarLoc = scala.util.Properties.envOrElse("JLINK_JAR_LOCATION",  null);
  if(jlinkJarLoc == null) throw new Exception("Need JLINK_JAR_LOCATION environmental variable set to location of the Mathematica JLink.jar file.");
  unmanagedJars in Compile += file(jlinkJarLoc)
}
