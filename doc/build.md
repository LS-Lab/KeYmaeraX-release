# Build instructions

This is a guide to building the various artifacts this repository provides.

You will need the following tools for most artifacts:

- JDK 8
- [sbt](https://www.scala-sbt.org/)
- [Mathematica](https://www.wolfram.com/mathematica/)
  or the [Wolfram Engine](https://www.wolfram.com/engine/)

## KeYmaera X with and without web UI

KeYmaera X can be used as CLI application or via a web UI.
Because the web UI adds size and startup time overhead,
two different jar files can be created:

- `keymaerax-core-<version>.jar` includes just a CLI.
- `keymaerax-webui-<version>.jar` includes both a CLI and a web UI.

First, copy the `default.properties` file to `local.properties`
and edit `mathematica.jlink.path` to point to the `JLink.jar` from your Mathematica or Wolfram Engine installation.
If you installed Mathematica at the
[default path](https://reference.wolfram.com/language/tutorial/WolframSystemFileOrganization.html),
the `JLink.jar` file is located at

- `/usr/local/Wolfram/Mathematica/13.0/SystemFiles/Links/JLink/JLink.jar` on Linux
- `/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/JLink.jar` on macOS
- `C:\Program Files\Wolfram Research\Mathematica\13.0\SystemFiles\Links\Jlink\Jlink.jar` on Windows

To create both jar files, run `sbt --mem 2048 assembly`.  
To create just the core jar file, run `sbt --mem 2048 'project core' assembly`.  
To create just the webui jar file, run `sbt --mem 2048 'project webui' assembly`.  
To clean up build files, run `sbt clean`.

The core jar file can be found at `keymaerax-core/target/scala-<scala version>/keymaerax-core-<version>.jar`.  
The webui jar file can be found at `keymaerax-webui/target/scala-<scala version>/keymaerax-webui-<version>.jar`.  

## Tests

To run a quick smoke test suite, run:
```shell
sbt "testOnly \
  -n edu.cmu.cs.ls.keymaerax.tags.SummaryTest \
  -n edu.cmu.cs.ls.keymaerax.tags.CheckinTest"
```

To run the full but lengthy test suite, run:
```shell
sbt "test \
  -l edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest"
```
To leave out slower tests, run:
```shell

sbt "testOnly \
  -l edu.cmu.cs.ls.keymaerax.tags.SlowTest \
  -l edu.cmu.cs.ls.keymaerax.tags.ExtremeTest \
  -l edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest \
  -l edu.cmu.cs.ls.keymaerax.tags.TodoTest"
```

To run a single test (e.g. `BenchmarkTests`), run:
```shell
sbt "testOnly edu.cmu.cs.ls.keymaerax.btactics.BenchmarkTests"
```
You can also use wildcards:
```shell
sbt "testOnly *USubst*"
```

Of course, you can also use all these commands in the interactive sbt shell:
```sbt
testOnly edu.cmu.cs.ls.keymaerax.btactics.BenchmarkTests
testOnly *USubst*
```

In general, `-n` specifies tags to include while `-l` specifies tags to exclude.
If no `-n` is specified, all tests are included by default.
For more details on running tests, see the
[ScalaTest documentation on using scalatest with sbt](https://www.scalatest.org/user_guide/using_scalatest_with_sbt).

## Documentation

Run `sbt unidoc` in the project root.
This will generate offline documentation at
[`target/scala-2.12/unidoc/index.html`](target/scala-2.12/unidoc/index.html).
