name := "KeYmaeraX"

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.10.4"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.10.4"

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.2.4" % "test"

libraryDependencies += "org.pegdown" % "pegdown" % "1.5.0" % "test"      // (For Html Scalatest reports)

libraryDependencies += "org.scalamock" %% "scalamock-scalatest-support" % "3.2" % "test"

/// mongodb driver

libraryDependencies += "org.mongodb" %% "casbah" % "2.7.4"

/// sqlite driver

libraryDependencies += "com.typesafe.slick" %% "slick" % "2.1.0"

libraryDependencies += "com.typesafe.slick" %% "slick-codegen" % "2.1.0"

//libraryDependencies += "org.scalaquery" %% "scalaquery" % "0.9.5"

libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.7.2"

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


//unmanagedResourceDirectories in Compile <++= baseDirectory map { 
//  path => ((path / "src/main/scala") ** "*.txt").get 
//}

//unmanagedResourceDirectories in Compile <+= baseDirectory {_ / "src/main/scala"}

//unmanagedResourceDirectories in Compile += baseDirectory.value / "src/main/scala"
//unmanagedResourceDirectories in Test += baseDirectory.value / "src/main/scala"

// def axiomSources = (baseDirectory.value / "src/main/scala" ##) ** "*.txt"
// override def mainResources = super.mainResources +++ axiomSources

////////////////////////////////////////////////////////////////////////////////
// Unit testing
////////////////////////////////////////////////////////////////////////////////

parallelExecution in Test := false

fork in Test := true

testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-h", "target/test-reports")

////////////////////////////////////////////////////////////////////////////////
// Builds -- make sure you are using SBT 13.6+
////////////////////////////////////////////////////////////////////////////////

//mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.hydra.Boot")

mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.Main")


test in assembly := {}

