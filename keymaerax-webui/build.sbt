name := "KeYmaeraX-Web"

version := "4.0a4"

//scalacOptions ++= Seq("-Xno-patmat-analysis")

assemblyJarName in assembly := "keymaerax-web-" + version.value + ".jar"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.7"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.11.7"

libraryDependencies += "org.scalatest" % "scalatest_2.11" % "2.2.4" % "test"

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
// HyDRA Settings
// Taken from https://www.assembla.com/wiki/show/liftweb/using_sbt
////////////////////////////////////////////////////////////////////////////////

resolvers += "Typesafe Repo" at "http://repo.typesafe.com/typesafe/releases/" // contains json-schema-validtor.

scalacOptions := Seq("-unchecked", "-deprecation", "-encoding", "utf8")

javaOptions += "-Xss20M"

libraryDependencies ++= {
  val akkaV = "2.3.12"
  val sprayV = "1.3.1"
  Seq(
    "io.spray"            %%  "spray-json"    % "1.3.2",
    "io.spray"            %%   "spray-can"     % sprayV,
    "io.spray"            %%   "spray-routing" % sprayV,
    //"io.spray"            %%   "spray-testkit" % sprayV  % "test",
    "com.typesafe.akka"   %%  "akka-actor"    % akkaV,
    //"com.typesafe.akka"   %  "akka-testkit"  % akkaV   % "test",
    //"org.specs2"          % "specs2-core"    % "3.6.4" % "test",
    "com.github.fge"      % "json-schema-validator" % "2.2.6" // only update to even-numbered versions please.
  )
}

//libraryDependencies += "net.liftweb" % "lift-json" % "latest.release" 

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

testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-h", "target/test-reports")

////////////////////////////////////////////////////////////////////////////////
// Builds -- make sure you are using SBT 13.6+
////////////////////////////////////////////////////////////////////////////////

// command line UI
mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX")

test in assembly := {}

