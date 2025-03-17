import java.io.{FileInputStream, InputStreamReader}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import java.util.Properties

ThisBuild / scalaVersion := "3.6.4"
ThisBuild / version := "5.1.2"

ThisBuild / scalacOptions ++= Seq(
  // Always show all non-suppressed warnings. See `scalac -Wconf:help` for more info.
  // https://www.scala-lang.org/2021/01/12/configuring-and-suppressing-warnings.html
  "-Wconf:any:w",
)

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

lazy val core = project
  .in(file("keymaerax-core"))
  .enablePlugins(BuildInfoPlugin)
  .settings(
    name := "KeYmaeraX Core",
    mainClass := Some("org.keymaerax.cli.KeymaeraxCore"),

    libraryDependencies += ("cc.redberry" %% "rings.scaladsl" % "2.5.8").cross(CrossVersion.for3Use2_13),
    libraryDependencies += "com.github.scopt" %% "scopt" % "4.1.0",
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "3.1.1",
    libraryDependencies += "io.github.classgraph" % "classgraph" % "4.8.179",
    libraryDependencies += "io.spray" %% "spray-json" % "1.3.6",
    libraryDependencies += "org.apache.commons" % "commons-configuration2" % "2.11.0",
    libraryDependencies += "org.apache.commons" % "commons-lang3" % "3.17.0",
    libraryDependencies += "org.typelevel" %% "paiges-core" % "0.4.4",
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
    // https://www.slf4j.org/manual.html#projectDep
    // https://github.com/lightbend-labs/scala-logging
    // https://www.baeldung.com/slf4j-with-log4j2-logback#Log4j2
    libraryDependencies += "org.slf4j" % "slf4j-api" % "2.0.17", // Force slf4j 2
    libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.9.5",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-api" % "2.24.3",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-core" % "2.24.3",
    libraryDependencies += "org.apache.logging.log4j" % "log4j-slf4j2-impl" % "2.24.3",

    // A published version of scala-smtlib that works with Scala 2.13
    // https://github.com/regb/scala-smtlib/issues/46#issuecomment-955691728
    // https://mvnrepository.com/artifact/com.regblanc/scala-smtlib_2.13/0.2.1-42-gc68dbaa
    libraryDependencies += ("com.regblanc" %% "scala-smtlib" % "0.2.1-42-gc68dbaa").cross(CrossVersion.for3Use2_13),

    Compile / run / mainClass := mainClass.value,
    assembly / mainClass := mainClass.value,
    assembly / assemblyJarName := s"${normalizedName.value}-${version.value}.jar",

    // Include version number as constant in source code
    buildInfoKeys := Seq[BuildInfoKey](
      version,
      "copyright" -> Files.readString(Paths.get("COPYRIGHT.txt")),
      "license" -> Files.readString(Paths.get("LICENSE.txt")),
      "licensesThirdParty" -> Files.readString(Paths.get("LICENSES_THIRD_PARTY.txt")),
    ),
    buildInfoPackage := "org.keymaerax.info",
    buildInfoOptions += BuildInfoOption.PackagePrivate,

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
  .dependsOn(core)
  .settings(
    name := "KeYmaeraX WebUI",
    mainClass := Some("org.keymaerax.cli.KeymaeraxWebui"),

    /// sqlite driver
    libraryDependencies += "com.typesafe.slick" %% "slick" % "3.5.2",
    libraryDependencies += "com.typesafe.slick" %% "slick-codegen" % "3.5.2",
    libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.48.0.0",

    // Akka
    libraryDependencies += "com.typesafe.akka" %% "akka-http" % "10.5.3",
    libraryDependencies += "com.typesafe.akka" %% "akka-http-spray-json" % "10.5.3",
    libraryDependencies += "com.typesafe.akka" %% "akka-http-xml" % "10.5.3",
    libraryDependencies += "com.typesafe.akka" %% "akka-slf4j" % "2.8.8",
    libraryDependencies += "com.typesafe.akka" %% "akka-stream" % "2.8.8",
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

    libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.19" % Test,
    libraryDependencies += "org.scalamock" %% "scalamock" % "6.1.1" % Test,

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
  .aggregate(core, webui)
  .enablePlugins(ScalaUnidocPlugin)
  .disablePlugins(AssemblyPlugin)
  .settings(
    name := "KeYmaeraX",

    Compile / doc / scalacOptions ++= Seq("-doc-root-content", "rootdoc.txt"),
  )
