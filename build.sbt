import java.io.{FileInputStream, InputStreamReader}
import java.nio.charset.StandardCharsets
import java.util.Properties

ThisBuild / scalaVersion := "2.13.12"
// TODO Use this version number in keymaerax-core
ThisBuild / version := "5.0.2"

ThisBuild / scalacOptions ++= {
  // Keymaerax has lots of warnings. Due to their volume, important warnings vanish between not-so-important ones.
  // To make warnings useful again, this code hides the most common warnings.
  // Over time, they should be re-enabled again and fixed.
  //
  // See `scalac -Wconf:help` for more details on how to write filters.
  // See also: https://www.scala-lang.org/2021/01/12/configuring-and-suppressing-warnings.html
  val warnings = Seq(
    // Never silence warnings in the core
    "site=edu.cmu.cs.ls.keymaerax.core.*:w",

    // Silence all deprecation warnings originating from @deprecated annotations inside keymaerax itself
    "cat=deprecation&origin=edu.cmu.cs.ls.keymaerax.*:s",

    // Silence match exhaustivity warnings
    "cat=other-match-analysis:s",
    "cat=unchecked&msg=Exhaustivity analysis:s",

    // Silence type erasure warnings
    "cat=unchecked&msg=erasure:s",

    // Silence warning about ClassfileAnnotation in macro subproject
    // TODO Remove when preparing macros for Scala 3
    "origin=scala.annotation.ClassfileAnnotation:s",

    // Default configuration, see -Wconf:help
    "cat=deprecation:ws",
    "cat=feature:ws",
    "cat=optimizer:ws",
  )
  Seq(
    s"-Wconf:${warnings.mkString(",")}",
    "-Xmaxwarns", "1000",
    "-Ymacro-annotations",
  )
}

// Never execute tests in parallel across all sub-projects
Global / concurrentRestrictions += Tags.limit(Tags.Test, 1)

lazy val macros = project
  .in(file("keymaerax-macros"))
  .disablePlugins(AssemblyPlugin)
  .settings(
    name := "KeYmaeraX Macros",

    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,
  )

lazy val core = project
  .in(file("keymaerax-core"))
  .dependsOn(macros)
  .settings(
    name := "KeYmaeraX Core",
    mainClass := Some("edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX"),

    libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value,

    libraryDependencies += "biz.enef" %% "slogging-slf4j" % "0.6.2",
    libraryDependencies += "cc.redberry" %% "rings.scaladsl" % "2.5.8",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.0.2",
    libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.1-42-gc68dbaa",
    libraryDependencies += "io.spray" %% "spray-json" % "1.3.6",
    libraryDependencies += "org.apache.commons" % "commons-configuration2" % "2.5",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-slf4j-impl" % "2.17.1",
    libraryDependencies += "org.reflections" % "reflections" % "0.10.2",
    libraryDependencies += "org.typelevel" %% "paiges-core" % "0.2.4",
    libraryDependencies += "org.typelevel" %% "spire" % "0.18.0",

    Compile / run / mainClass := mainClass.value,
    assembly / mainClass := mainClass.value,
    assembly / assemblyJarName := s"${normalizedName.value}-${version.value}.jar",

    // Use Mathematica's JLink.jar as unmanaged dependency
    // The path is read from the property mathematica.jlink.path in the file local.properties
    Compile / unmanagedJars += {
      val properties = new Properties()
      try {
        val stream = new FileInputStream("local.properties")
        val reader = new InputStreamReader(stream, StandardCharsets.UTF_8)
        properties.load(reader)
      } catch {
        case e: Throwable => throw new Exception("Failed to load file local.properties", e)
      }
      val jlinkPath: String = properties.getProperty("mathematica.jlink.path")
      if (jlinkPath == null) {
        throw new Exception("Property mathematica.jlink.path not found in file local.properties")
      }
      file(jlinkPath)
    },
  )

lazy val webui = project
  .in(file("keymaerax-webui"))
  .dependsOn(macros, core)
  .settings(
    name := "KeYmaeraX WebUI",
    mainClass := Some("edu.cmu.cs.ls.keymaerax.launcher.Main"),

    /// sqlite driver
    libraryDependencies += "com.typesafe.slick" %% "slick" % "3.4.1",
    libraryDependencies += "com.typesafe.slick" %% "slick-codegen" % "3.4.1",
    libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.27.2", // For SqliteTableGenerator

    // Akka
    libraryDependencies += "com.typesafe.akka" %% "akka-http" % "10.5.3",
    libraryDependencies += "com.typesafe.akka" %% "akka-http-spray-json" % "10.5.3",
    libraryDependencies += "com.typesafe.akka" %% "akka-http-xml" % "10.5.3",
    libraryDependencies += "com.typesafe.akka" %% "akka-slf4j" % "2.8.5",
    libraryDependencies += "com.typesafe.akka" %% "akka-stream" % "2.8.5",
    libraryDependencies += "io.spray" %% "spray-json" % "1.3.6",

    Compile / run / mainClass := mainClass.value,
    assembly / mainClass := mainClass.value,
    assembly / assemblyJarName := s"${normalizedName.value}-${version.value}.jar",

    // Include some resources as triggers for triggered execution (~)
    watchTriggers += baseDirectory.value.toGlob / "src" / "main" / "resources" / "partials" / "*.html",
    watchTriggers += baseDirectory.value.toGlob / "src" / "main" / "resources" / "js" / "*.{js,map}",
    watchTriggers += baseDirectory.value.toGlob / "src" / "main" / "resources" / "*.html",

    /////////////
    // Testing //
    /////////////

    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.8" % Test,
    libraryDependencies += "org.scalamock" %% "scalamock" % "4.4.0" % Test,
    libraryDependencies += "org.pegdown" % "pegdown" % "1.6.0" % Test, // (For Html Scalatest reports)

    Test / parallelExecution := false,

    // set fork to true in order to run tests in their own Java process.
    // not forking avoids broken pipe exceptions in test reporter, but forking might become necessary in certain
    // multithreaded setups (see ScalaTest documentation)
    Test / fork := false,

    // set HTML test report output directory
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-h", "target/test-reports"),

    // record and report test durations
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-oD"),

    // report long-running tests (report every hour for tests that run longer than 1hr)
    Test / testOptions += Tests.Argument(TestFrameworks.ScalaTest, "-W", "3600", "3600"),

    resolvers ++= Resolver.sonatypeOssRepos("snapshots"), // ScalaMeter
    testFrameworks += new TestFramework("org.scalameter.ScalaMeterFramework"),

    logBuffered := false,

    // Include test resources in uberjar created via `sbt Test/assembly`.
    // In particular, this includes test/resources/examples over src/resources/examples.
    inConfig(Test)(AssemblyPlugin.assemblySettings),
    Test / assemblyMergeStrategy := {
      case PathList("examples", _*) => MergeStrategy.last
      case path => MergeStrategy.defaultMergeStrategy(path)
    },
  )

// build KeYmaera X full jar with sbt clean assembly
lazy val root = project
  .in(file("."))
  .aggregate(macros, core, webui)
  .enablePlugins(ScalaUnidocPlugin)
  .disablePlugins(AssemblyPlugin)
  .settings(
    name := "KeYmaeraX",

    Compile / doc / scalacOptions ++= Seq("-doc-root-content", "rootdoc.txt"),
    ScalaUnidoc / unidoc / scalacOptions += "-Ymacro-expand:none",
    ScalaUnidoc / unidoc / unidocProjectFilter := inAnyProject -- inProjects(macros),
  )
