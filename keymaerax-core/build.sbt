name := "KeYmaeraX Core"

version := "4.0a4"

scalaVersion := "2.11.6"

//parser combinators are not longer included by default.
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

////////////////////////////////////////////////////////////////////////////////
// Mathematica Interop
////////////////////////////////////////////////////////////////////////////////
{
  val jlinkJarLoc = scala.util.Properties.envOrElse("JLINK_JAR_LOCATION",  null);
  if(jlinkJarLoc == null) throw new Exception("Need JLINK_JAR_LOCATION environmental variable set to location of the Mathematica JLINK JAR file.");
  unmanagedJars in Compile += file(jlinkJarLoc)
}


//Options for JLINK_JAR_LOCATION:
//// >= 10.0.2
//unmanagedJars in Compile += file("/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/JLink.jar")
//
//// <= 10.0.1
//unmanagedJars in Compile += file("/Applications/Mathematica.app/SystemFiles/Links/JLink/JLink.jar")
//
//// Linux
//unmanagedJars in Compile += file("/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/JLink.jar")
//
//unmanagedJars in Compile += file("/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/JLink.jar")
