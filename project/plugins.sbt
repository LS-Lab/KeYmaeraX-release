addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "2.2.0")
addSbtPlugin("com.github.sbt" % "sbt-unidoc" % "0.5.0")

// Provide sbt build info (like the version number) as constants in the source code
// https://github.com/sbt/sbt-buildinfo
addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.12.0")

// Always display all warnings, even for unchanged files.
addSbtPlugin("com.timushev.sbt" % "sbt-rewarn" % "0.1.3")

// Format source files
// See docs for usage and additional info:
// https://scalameta.org/scalafmt/docs/installation.html#sbt
addSbtPlugin("org.scalameta" % "sbt-scalafmt" % "2.5.2")
