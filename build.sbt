import java.io.{FileInputStream, InputStreamReader}
import java.nio.charset.StandardCharsets
import java.util.Properties

ThisBuild / scalaVersion := "2.13.13"
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

ThisBuild / assemblyMergeStrategy := {
  // Multiple dependency jars have a module-info.class file in the same location.
  // Without custom rules, they cause merge conflicts with sbt-assembly.
  // Since we're building an uberjar, it should be safe to discard them (according to stackoverflow).
  // https://stackoverflow.com/a/55557287
  case PathList(elements @ _*) if elements.last == "module-info.class" => MergeStrategy.discard

  // https://github.com/sbt/sbt-assembly#merge-strategy
  case path =>
    val oldStrategy = (ThisBuild / assemblyMergeStrategy).value
    oldStrategy(path)
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
  .enablePlugins(BuildInfoPlugin)
  .dependsOn(macros)
  .settings(
    name := "KeYmaeraX Core",
    mainClass := Some("edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX"),

    libraryDependencies += "org.scala-lang" % "scala-compiler" % scalaVersion.value,

    libraryDependencies += "cc.redberry" %% "rings.scaladsl" % "2.5.8",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.1.0",
    libraryDependencies += "io.spray" %% "spray-json" % "1.3.6",
    libraryDependencies += "org.apache.commons" % "commons-configuration2" % "2.5",
    libraryDependencies += "org.reflections" % "reflections" % "0.10.2",
    libraryDependencies += "org.typelevel" %% "paiges-core" % "0.4.3",
    libraryDependencies += "org.typelevel" %% "spire" % "0.18.0",

    // Logging
    //
    // KeYmaera X and some of its dependencies use slf4j for logging.
    // Slf4j is a facade for various logging frameworks called "providers".
    // Forcing slf4j 2 usually works fine for dependencies that create logs,
    // but forcing an slf4j 1 provider to use slf4j 2 will break things.
    // Since some dependencies updated to slf4j 2 already, we have to use an slf4j 2 provider
    // and force all other dependencies to use slf4j 2 as well via sbt's default version conflict resolution.
    //
    // https://github.com/jokade/slogging?tab=readme-ov-file#getting-started
    // https://www.baeldung.com/slf4j-with-log4j2-logback#Log4j2
    libraryDependencies += "biz.enef" %% "slogging-slf4j" % "0.6.2",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-api" % "2.23.1",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-core" % "2.23.1",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-slf4j2-impl" % "2.23.1",

    // A published version of scala-smtlib that works with Scala 2.13
    // https://github.com/regb/scala-smtlib/issues/46#issuecomment-955691728
    // https://mvnrepository.com/artifact/com.regblanc/scala-smtlib_2.13/0.2.1-42-gc68dbaa
    libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.1-42-gc68dbaa",

    Compile / run / mainClass := mainClass.value,
    assembly / mainClass := mainClass.value,
    assembly / assemblyJarName := s"${normalizedName.value}-${version.value}.jar",

    // Include version number as constant in source code
    buildInfoKeys := Seq[BuildInfoKey](version),
    buildInfoPackage := "edu.cmu.cs.ls.keymaerax",

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
    libraryDependencies += "com.typesafe.slick" %% "slick" % "3.5.1",
    libraryDependencies += "com.typesafe.slick" %% "slick-codegen" % "3.5.1",
    libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.45.3.0",

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

    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.18" % Test,
    libraryDependencies += "org.scalamock" %% "scalamock" % "5.2.0" % Test,

    // For generating HTML scalatest reports using the `-h <directory>` flag
    // See "Using Reporters" in https://www.scalatest.org/user_guide/using_scalatest_with_sbt
    // https://stackoverflow.com/a/59059383
    // https://github.com/scalatest/scalatest/issues/1736
    libraryDependencies += "com.vladsch.flexmark" % "flexmark-all" % "0.64.8" % Test,

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
