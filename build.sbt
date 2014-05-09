scalaVersion := "2.10.4"

libraryDependencies += "org.scala-lang" % "scala-swing" % "2.10.4"

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.0" % "test"

unmanagedJars in Compile += file("/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/JLink.jar")

unmanagedJars in Compile += file("/Applications/Mathematica.app/SystemFiles/Links/JLink/JLink.jar")
