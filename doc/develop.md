# Developing KeYmaera X

To set up a development environment, first follow the [build instructions](build.md).
Then follow the instructions for setting up your IDE below.
We strongly recommend using IntelliJ IDEA and its Scala plugin.

Also make sure to read the [coding conventions](../CodingConventions.md).

**WARNING:**
The KeYmaera X project currently does not accept outside contributions,
meaning pull requests on the `KeYmaeraX-release` repo won't be merged.
However, issues are always welcome!

## IntelliJ IDEA

**If you already set up this project before,**
close IDEA and run `git clean -dfx .idea/` in the project root
to reset your project-specific settings before following the steps below.

1. Install IDEA's Scala plugin.
2. Open the project directory in IDEA.
3. Wait for IDEA to import the project.
  If this fails, ensure the project SDK at
  `File | Project Structure | Project Settings | Project`
  is set to the JDK from the compilation instructions and restart IDEA.
4. In `File | Settings | Build, Execution, Deployment | Build Tools | sbt`,
  set the checkmarks for *builds* and *Enable debugging* in the *sbt shell* section.
5. In `File | Settings | Tools | Actions on Save`,
  enable the checkbox for *Update copyright notice*.
