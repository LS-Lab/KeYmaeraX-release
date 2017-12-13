import java.io.{BufferedReader, FileReader}

name := "KeYmaeraX-Web"

version := new BufferedReader(new FileReader("keymaerax-core/src/main/resources/VERSION")).readLine()

//scalacOptions ++= Seq("-Xno-patmat-analysis")

resolvers += "Sonatype OSS Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots" // ScalaMeter

assemblyJarName in (Test, assembly) := s"keymaerax-${version.value}.jar"

scalacOptions in (Compile, doc) ++= Seq("-doc-root-content", "rootdoc.txt")

libraryDependencies += "org.scala-lang" % "scala-reflect" % "2.11.7"

libraryDependencies += "org.scala-lang" % "scala-compiler" % "2.11.7"

libraryDependencies += "org.scalatest" % "scalatest_2.11" % "3.0.1" % "test"

libraryDependencies += "org.pegdown" % "pegdown" % "1.5.0" % "test"      // (For Html Scalatest reports)

/// sqlite driver

libraryDependencies += "com.typesafe.slick" %% "slick" % "2.1.0"

libraryDependencies += "com.typesafe.slick" %% "slick-codegen" % "2.1.0"

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
    "com.typesafe.akka"   %% "akka-slf4j"     % akkaV,
    "ch.qos.logback"      % "logback-classic" % "1.0.13",
    //"com.typesafe.akka"   %  "akka-testkit"  % akkaV   % "test",
    //"org.specs2"          % "specs2-core"    % "3.6.4" % "test",
    "com.github.fge"      % "json-schema-validator" % "2.2.6" // only update to even-numbered versions please.
  )
}

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

fork in Test := false // set fork to true in order to run tests in their own Java process

//@todo reenable once unserializable exceptions fixed:
// testOptions in Test += Tests.Argument(TestFrameworks.ScalaTest, "-h", "target/test-reports")

testFrameworks += new TestFramework("org.scalameter.ScalaMeterFramework")

logBuffered := false

////////////////////////////////////////////////////////////////////////////////
// Builds -- make sure you are using SBT 13.6+
////////////////////////////////////////////////////////////////////////////////

// command line UI
mainClass in assembly := Some("edu.cmu.cs.ls.keymaerax.launcher.Main")
// ACAS X: run sbt test:assembly to build assembly
//mainClass in (Test, assembly) := Some("edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable.AcasXRunner")

// do not run tests when building assembly
test in assembly := {}
