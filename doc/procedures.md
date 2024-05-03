# Procedures

This file describes step-by-step procedures related to this repository and its maintenance.

## Set up build environment

This is a guide for setting up a build environment for KeYmaera X.
These steps are required if you want to do more than just looking at the source code.

### 1. Install required tools

Install the following tools:

- JDK 21
- [sbt](https://www.scala-sbt.org/)
- [Mathematica](https://www.wolfram.com/mathematica/)
  or the [Wolfram Engine](https://www.wolfram.com/engine/)

### 2. Clone this repo

Assuming you have not already done so, clone this repo to a path of your choice.
Any commands in this guide assume they're being executed in the root of the repository unless specified otherwise.

Some commits should be omitted from `git blame` by default
(e.g. reformatting commits that don't meaningfully change the code).
To configure your local repository to ignore them, use the following command:

```shell
git config blame.ignoreRevsFile .git-blame-ignore-revs
```

### 3. Clone example projects

Clone the [KeYmaeraX-projects](https://github.com/LS-Lab/KeYmaeraX-projects) repo
to `keymaerax-webui/src/main/resources/keymaerax-projects` using the following command:

```shell
git clone https://github.com/LS-Lab/KeYmaeraX-projects keymaerax-webui/src/main/resources/keymaerax-projects
```

### 4. Prepare `local.properties`

KeYmaera X has optional support of Wolfram Mathematica or Wolfram Engine at runtime.
However, during compilation, Mathematica's `JLink.jar` file is required.
At this time, there is no support for compiling without this file.

Copy the `default.properties` file to `local.properties`
and edit `mathematica.jlink.path` to point to the `JLink.jar` from your Mathematica or Wolfram Engine installation.
If you installed Mathematica at the
[default path](https://reference.wolfram.com/language/tutorial/WolframSystemFileOrganization.html),
the `JLink.jar` file is located at

- `/usr/local/Wolfram/Mathematica/13.0/SystemFiles/Links/JLink/JLink.jar` on Linux
- `/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/JLink.jar` on macOS
- `C:\Program Files\Wolfram Research\Mathematica\13.0\SystemFiles\Links\Jlink\Jlink.jar` on Windows

## Set up dev environment

This is a guide for setting up a dev environment including IDE for KeYmaera X.
Only [IntelliJ IDEA](https://www.jetbrains.com/idea/) is officially supported.

### 1. Set up build environment

First, follow the steps to [set up a build environment](#set-up-build-environment).

### 2. Set up IntelliJ IDEA

**If you already opened this project in IDEA before,**
close IDEA and run `git clean -dfx .idea/` to reset your project-specific settings.
This can help prevent weird setup issues.

Then, follow these steps:

1. Install IDEA's Scala plugin.
2. Open the project directory in IDEA.
3. Import the sbt project.
   Usually, IDEA will prompt whether you want to do so.
   If the import fails, ensure the project SDK at `File | Project Structure | Project Settings | Project`
   is set to the JDK from the compilation instructions and restart IDEA.
4. In `File | Settings | Build, Execution, Deployment | Build Tools | sbt`,
   set the checkmarks for *builds* and *Enable debugging* in the *sbt shell* section.
5. In `File | Settings | Tools | Actions on Save`, enable the checkbox for *Update copyright notice*.

## Build jar files

KeYmaera X can be used as CLI application or via a web UI.
Because the web UI adds size and startup time overhead, two different jar files can be created:

- `keymaerax-core-<version>.jar` includes just a CLI.
- `keymaerax-webui-<version>.jar` includes both a CLI and the web UI.

To create both jar files, run:

```shell
sbt --mem 2048 assembly
```

To create just the core jar file, run:

```shell
sbt --mem 2048 'project core' assembly
```

To create just the webui jar file, run:

```shell
sbt --mem 2048 'project webui' assembly
```

The core jar file will be located at `keymaerax-core/target/scala-<scala version>/keymaerax-core-<version>.jar`.  
The webui jar file will be located at `keymaerax-webui/target/scala-<scala version>/keymaerax-webui-<version>.jar`.

To clean up all build files, run:

```shell
sbt clean
```

## Build HTML documentation

To generate documentation from the source code, run:

```shell
sbt unidoc
```

The generated documentation will be located at `target/scala-<scala version>/unidoc/index.html`.

## Check for warnings and errors

To check whether source code changes introduced any warnings or errors, run:

```shell
sbt --mem 2048 compile Test/compile
```

## Run tests

To run a quick smoke test suite, run:

```shell
sbt "testOnly -- \
  -n edu.cmu.cs.ls.keymaerax.tags.SummaryTest \
  -n edu.cmu.cs.ls.keymaerax.tags.CheckinTest \
  -l edu.cmu.cs.ls.keymaerax.tags.TodoTest"
```

To run the full but lengthy test suite, run:

```shell
sbt "test -- \
  -l edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest \
  -l edu.cmu.cs.ls.keymaerax.tags.TodoTest"
```

To leave out slower tests, run:

```shell

sbt "test -- \
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

```shell
testOnly edu.cmu.cs.ls.keymaerax.btactics.BenchmarkTests
testOnly *USubst*
```

In general, `-n` specifies tags to include while `-l` specifies tags to exclude.
If no `-n` is specified, all tests are included by default.
For more details on running tests, see the ScalaTest documentation
on [using scalatest with sbt](https://www.scalatest.org/user_guide/using_scalatest_with_sbt).

## Format source files

To format all source files with `scalafmt`, run:

```shell
sbt scalafmt Test/scalafmt
```

To check if files are formatted correctly, run:

```shell
sbt scalafmtCheck Test/scalafmtCheck
```

When editing code with IDEA, files are formatted with `scalafmt`
when you save with `Ctrl+S` or format with `Ctrl+Alt+L`.