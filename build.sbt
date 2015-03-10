scalaVersion := "2.10.4"

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.10.4"

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.0" % "test"

libraryDependencies += "org.scalamock" %% "scalamock-scalatest-support" % "3.2" % "test"

/// mongodb driver

libraryDependencies += "org.mongodb" %% "casbah" % "2.7.4"

////////////////////////////////////////////////////////////////////////////////
// Mathematica Interop
////////////////////////////////////////////////////////////////////////////////

// >= 10.0.2
unmanagedJars in Compile += file("/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/JLink.jar")

// <= 10.0.1
unmanagedJars in Compile += file("/Applications/Mathematica.app/SystemFiles/Links/JLink/JLink.jar")

// Linux
unmanagedJars in Compile += file("/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/JLink.jar")

unmanagedJars in Compile += file("/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/JLink.jar")

////////////////////////////////////////////////////////////////////////////////
// Hyrda Settings
// Taken from https://www.assembla.com/wiki/show/liftweb/using_sbt
////////////////////////////////////////////////////////////////////////////////

resolvers += "Typesafe Repo" at "http://repo.typesafe.com/typesafe/releases/" // contains json-schema-validtor.

scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8")

javaOptions += "-Xss20M"

libraryDependencies ++= {
  val akkaV = "2.1.4"
  val sprayV = "1.1.1"
  Seq(
    "io.spray"            %%  "spray-json"    % "1.2.6",
    "io.spray"            %   "spray-can"     % sprayV,
    "io.spray"            %   "spray-routing" % sprayV,
    "io.spray"            %   "spray-testkit" % sprayV  % "test",
    "com.typesafe.akka"   %%  "akka-actor"    % akkaV,
    "com.typesafe.akka"   %%  "akka-testkit"  % akkaV   % "test",
    "org.specs2"          %%  "specs2"        % "2.2.3" % "test",
    "com.github.fge"      % "json-schema-validator" % "2.2.6" // only update to even-numbered versions please.
  )
}

//libraryDependencies += "net.liftweb" % "lift-json" % "latest.release" 

Revolver.settings

////////////////////////////////////////////////////////////////////////////////
// Continuous testing/running settgings (i.e., definiting behavior of the ~
// command
////////////////////////////////////////////////////////////////////////////////

watchSources <++= baseDirectory map { 
  path => ((path / "src/main/resources/partials/") ** "*.html").get 
}

watchSources <++= baseDirectory map { 
  path => ((path / "src/main/resources/js") ** "*.js").get 
}

watchSources <++= baseDirectory map { 
  path => ((path / "src/main/resources") ** "*.html").get 
}

////////////////////////////////////////////////////////////////////////////////
// Unit testing
////////////////////////////////////////////////////////////////////////////////

parallelExecution in Test := false

fork in Test := true

////////////////////////////////////////////////////////////////////////////////
// Builds -- make sure you are using SBT 13.6+
////////////////////////////////////////////////////////////////////////////////

mainClass in assembly := Some("edu.cmu.cs.ls.keymaera.hydra.Boot")

test in assembly := {}
