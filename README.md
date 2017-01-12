KeYmaera X
==========

KeYmaera X is a theorem prover for differential dynamic logic (dL), a logic for specifying and verifying properties of hybrid systems with mixed discrete and continuous dynamics. Reasoning about complicated hybrid systems models requires support for sophisticated proof techniques, efficient computation, and a user interface that crystallizes salient properties of the system. KeYmaera X allows users to specify custom proof search techniques as tactics, execute these tactics in parallel, and interface with partial proofs via an extensible user interface.

Advanced proof search features---and user-defined tactics in particular---are difficult to check for soundness. To admit extension and experimentation in proof search without reducing trust in the prover, KeYmaera X is built up from a small trusted kernel. The prover kernel contains a list of sound dL axioms that are instantiated using a uniform substitution proof rule. Isolating all soundness-critical reasoning to this prover kernel obviates the intractable task of ensuring that each new proof search algorithm is implemented correctly. Experiments suggest that a single layer of tactics on top of the prover kernel provides a rich language for implementing novel and sophisticated proof search techniques.

More information and precompiled binaries are available at:
  http://keymaeraX.org/

Installation
============
The easiest way to run KeYmaera X is to download binaries 
[keymaerax.jar](http://keymaerax.org/keymaerax.jar) and run it via

    java -jar keymaerax.jar

Ensure that the following software is installed
- [Java Development Kit JDK](https://java.com/download)
  (version 1.8+ recommended. Mathematica 9.0 is only compatible with Java 1.6 and 1.7. Mathematica 10.0+ are also compatible with Java 1.8)
- [Wolfram Mathematica](https://www.wolfram.com/mathematica/)
  (version 10+ recommended. Other versions may work.
  The Mathematica J/Link library that comes with Mathematica is needed during compilation. Mathematica needs to be activated to use it also at runtime.
  Otherwise [https://github.com/Z3Prover/z3](Z3) is automatically used for arithmetic.)

Building
========
To compile KeYmaera X from source code, install the above software and also install
- [Scala Build Tool sbt](http://www.scala-sbt.org)
  (Version 0.13 or greater recommended. Other versions may work).
  If you are using IntelliJ, this comes with the Scala plugin.
  http://www.scala-sbt.org/release/docs/Getting-Started/Setup.html

1) Compile KeYmaera X with the Scala Build Tool:

    sbt compile

2) Reinitialize the lemma database by deleting the KeYmaera X cache in your home directory and run the lemma initialization as follows:

    rm -rf ~/.keymaerax/cache
    sbt "test-only edu.cmu.cs.ls.keymaerax.btactics.DerivedAxiomsTests"

3) The Web UI web user interface of KeYmaera X can be started as follows:

    sbt assembly
    java -jar keymaerax.jar
    open http://localhost:8090/

If the jar does not start because of an error `no manifest found`, then first run `sbt clean`.
In case of errors about `invalid or corrupt jarfile`, please update Java to a newer version.

4) To find out how to use KeYmaera X from command line instead of the web user interface, run:

    java -Xss20M -jar keymaerax.jar -help

5) API documentation is provided at http://keymaeraX.org/scaladoc
  while local documentation will be generated in the directory `target/scala-2.11/unidoc` with:

    sbt unidoc

6) To test your installation, you can run the full regression test suite:

    sbt test -l edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest

##### FAQ: Build Problems
===================
The build file uses default paths to the Mathematica JLink JAR for MacOS and Mathematica 10 (see file `default.properties`).
If those are not suitable for your setup, create a file `local.properties` in the same directory as `default.properties`
(project root) and provide the location of JLink.jar with a property

    mathematica.jlink.path=YOUR_LOCAL_PATH_TO_JLINKJAR

If, at any time, you run into problems during the compilation process, use `sbt clean` for a fresh start to remove stale files. If the problems persist, use `sbt clean` followed by `sbt reload`. On a few computers you may have to edit your environment variables, e.g., `~/.bashrc` or  `~/.profile` to include something like

    export SBT_OPTS="-Xss20M -Xms8000M"

The Wiki contains extended build instructions and solutions to other
common sbt problems:

https://github.com/LS-Lab/KeYmaera4/wiki/Building-Instructions

##### FAQ: Run Problems
=================

If running `java -jar keymaerax.jar` results in the error `Invalid or corrupt jarfile` then update to Java 1.8 (and to Mathematic 10+)
or run KeYmaera X via

    java -Xss20M -cp keymaerax.jar KeYmaeraX

If KeYmaera X acts weird after an update, you should clean your local cache of lemmas by removing (or renaming) the directory `~/.keymaerax/cache`.
You could also try removing or renaming the model and proof database `~/.keymaerax/keymaerax.sqlite` (if this file has become corrupt, it may prevent KeYmaera X from working properly).

Errors related to JLinkNative Library are caused by incompatibilities of Java 1.8 in combination with Mathematica 9. It is recommended to use Mathematica 10.


IntelliJ IDEA Development Environment
=====================================

If you choose to use the IntelliJ IDEA development environment, install it:
- Install IntelliJ IDEA
- Install the Scala plugin for IntelliJ (the IntelliJ installer will ask you if you want to do this)

Project Setup
- Make sure you have defined the JLINK_JAR_LOCATION environment variable (see FAQ).
- Create a new Scala project, backed by SBT
- Select a JDK as your project SDK, add a new one if not previously added
- Check `update automatically` (not checked by default), so that updates to build.sbt are reflected automatically in the project. You may also want to check the "Download and compile sources" options.
- If the bundled version of sbt is not working for you, you can specify your own version here.

Create a new run configuration of type Application for the KeYmaera X Web UI.
- Main class: `edu.cmu.cs.ls.keymaerax.hydra.NonSSLBoot`
- Set the working directory to the project path
- Use the classpath of your project module
- Check "Single instance only"
- Make sure the JVM option `-Xss20M` is included in the run configuration.

Test Cases:
- Right click on project folder `keymaerax-webui/src/test` to mark this directory as Test Sources Root.
- Make sure the JVM option `-Xss20M` is included in the run configuration.
- Right click on the test folder to run all its ScalaTests.

Tagged Test Suite:
Run Configurations Drop-down in Toolbar
 -> Edit Configurations
 -> Add Configuration (ScalaTest)
 -> Select "All in package" for Test Kind
 -> Under "Test options" enter:
      `-n edu.cmu.cs.ls.keymaerax.tags.CheckinTest -n edu.cmu.cs.ls.keymaerax.tags.SummaryTest -l edu.cmu.cs.ls.keymaerax.tags.ObsoleteTest`
      (or any other string from `TestTags.scala`)
 -> Select "keymaerax" as SDK and classpath of module
 -> Apply/OK

##### IntelliJ FAQ
============
If, at any time, you run into problems during the compilation process in IntelliJ, check the `File->Project Structure->Modules->core->Dependencies` to make sure the appropriate files such as `SBT: unmanaged-jars` are checked. This is necessary for IntelliJ to find JLink.jar. IntelliJ keeps forgetting about it, so you may have to check repeatedly. If the problems persist, do `File->Invalidate Caches / Restart`.

Command Line Execution and Templates
====================================
For batch operation, KeYmaera X accepts models and tactics from the command line. Templates and example models can be
 found in

    keymaerax-webui/src/main/resources/cmdlinetemplates

This directory provides templates for models, tactics, and scripts for running KeYmaera X from the command line. It
further provides the example model from the KeYmaera X cheat sheet (CheatSheet.kyx), as well as tactics for proving
the cheat sheet model.

##### Files


| File                          | Description                                                                     |
| ----------------------------- | ------------------------------------------------------------------------------- |
| CheatSheet.kyx                | Model from page 1 http://keymaeraX.org/KeYmaeraX-sheet.pdf        |
| CheatSheetScriptTactic.scala  | A step-by-step proof script for proving CheatSheet.kyx                          |
| CheatSheetSearchyTactic.scala | A proof search tactic for proving CheatSheet.kyx                                |
| prove_script_macos_default.sh | Script to prove CheatSheet.kyx on MacOS with a default Mathematica installation |
| prove.sh                      | Template for starting the prover with a model and a tactic to produce a proof   |
| Template.kyx                  | Template for model files                                                        |
| TemplateTactic.scala          | Template for tactic files                                                       |

##### Configuration
KeYmaera X requires a decision procedure for real arithmetic to finalize proofs. It is tested best with Mathematica.
Depending on the operating system, Mathematica is installed in different locations. Adapt prove.sh to specify the
parameters -mathkernel and -jlink according to the local Mathematica setup. Parameters that are appropriate when
Mathematica is installed in the default location are provided below.

##### Default Configuration Parameters per Operating System
MacOS, 64bit, Mathematica 10.4
* `-mathkernel /Applications/Mathematica.app/Contents/MacOS/MathKernel`
* `-jlink /Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64`

Linux, 64bit, Mathematica 10.4
* `-mathkernel /usr/local/Wolfram/Mathematica/10.4/Executables/MathKernel`
* `-jlink /usr/local/Wolfram/Mathematica/10.4/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64`

Windows, 64bit, Mathematica 10.4
* `-mathkernel "C:\Program Files\Wolfram Research\Mathematica\10.4\MathKernel.exe"`
* `-jlink "C:\Program Files\Wolfram Research\Mathematica\10.4\SystemFiles\Links\JLink\SystemFiles\Libraries\Windows-x86-64"`

Source Code Layout
==================

KeYmaera X API Documentation explains the package layout: http://keymaeraX.org/scaladoc

`build.sbt` - SBT configuration file.

The project is split into two subprojects, `keymaerax-core` for the core functionalities of the prover and `keymaerax-webui` for everything else.

    keymaerax-core/src/ - Source code directory
    keymaerax-core/src/main/scala - source code (edu.cmu.cs.ls.keymaerax)
    keymaerax-webui/src/ - Source code directory for Web UI etc.
    keymaerax-webui/src/test/scala - tests run by `sbt test`
    keymaerax-core/target/scala-2.11/api/ - Target directory for sbt doc documentation.
    target/ - Generated files directory created by sbt on first compilation.
    target/scala-2.11/classes/ - Target directory for sbt compilation.    
    target/scala-2.11/unidoc/ - Target directory for sbt unidoc documentation.    

Test Cases
==========

The full test suite can be run from command line, e.g., by

    sbt test -l edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest 

Selectively running individual test cases within the sbt interactive mode:

    sbt
    sbt>  test-only *USubst*

Or, run on a more fine-grained level within a class use
object MyTest extends Tag("MyTest")

    object MyTest extends Tag("MyTest")
    it should "do something useful" taggedAs(MyTest) in {....}
    it should "do anything useful" taggedAs(MyTest) in {....}
    it should "do more good" taggedAs(MoreTest) in {....}

Then in sbt interactive mode run   

    sbt>  test-only -- -n "MyTest MoreTest"

To inline scala console output alongside the test suite information, first do:

    sbt>  set logBuffered in Test := false

IntelliJ IDEA can also run the test suite (see #IntelliJ IDEA).

The Wiki contains an introduction to the testing framework:
https://github.com/LS-Lab/KeYmaera4/wiki/How-to-Add-Tests
http://www.scalatest.org/user_guide


Specification
=============

The goal of KeYmaera X is to implement the proof calculus of differential dynamic logic in a way that is amenable to soundness assurance by way of a small trusted LCF-style kernel while still being amenable to automatic theorem proving.
Differential dynamic logic and its Hilbert-type and sequent proof calculi have been described and specified in more detail in:

1. André Platzer. 
[A complete uniform substitution calculus for differential dynamic logic](http://dx.doi.org/10.1007/s10817-016-9385-1). 
Journal of Automated Reasoning, 2016.

Based on: André Platzer. 
[A uniform substitution calculus for differential dynamic logic](http://dx.doi.org/10.1007/978-3-319-21401-6_32). 
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
Extended version at [arXiv 1503.01981](http://arxiv.org/abs/1503.01981)

2. André Platzer.
[Logics of dynamical systems](http://dx.doi.org/10.1109/LICS.2012.13).
ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012.

3. Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Völp and André Platzer. 
[KeYmaera X: An axiomatic tactical theorem prover for hybrid systems](http://dx.doi.org/10.1007/978-3-319-21401-6_36). 
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. 

4. André Platzer.
[Differential dynamic logic for hybrid systems](http://dx.doi.org/10.1007/s10817-008-9103-8).
Journal of Automated Reasoning, 41(2), pages 143-189, 2008.

5. André Platzer.
[Logical Analysis of Hybrid Systems: Proving Theorems for Complex Dynamics](http://dx.doi.org/10.1007/978-3-642-14509-4).
Springer, 2010. 426 p. ISBN 978-3-642-14508-7. 

6. André Platzer.
[Differential dynamic logic for verifying parametric hybrid systems](http://dx.doi.org/10.1007/978-3-540-73099-6_17).
In Nicola Olivetti, editor, Automated Reasoning with Analytic Tableaux and Related Methods, International Conference, TABLEAUX 2007, Aix en Provence, France, July 3-6, 2007, Proceedings, volume 4548 of LNCS, pages 216-232. Springer, 2007. 

The advanced proof techniques of differential invariants, differential cuts, and differential ghosts are described and specified in

7. André Platzer.
[The structure of differential invariants and differential cut elimination](http://dx.doi.org/10.2168/LMCS-8(4:16)2012).
Logical Methods in Computer Science, 8(4), pages 1-38, 2012. 

A secondary goal of KeYmaera X is to also make it possible to implement extensions of differential dynamic logic, such as differential game logic for hybrid games as well as quantified differential dynamic logic for distributed hybrid systems, which, along with its proof calculus, are described and specified in

8. André Platzer. 
[Differential game logic](http://dx.doi.org/10.1145/2817824). 
ACM Trans. Comput. Log., 17(1), 2015.

10. André Platzer.
[A complete axiomatization of quantified differential dynamic logic for distributed hybrid systems](http://dx.doi.org/10.2168/LMCS-8(4:17)2012).
Logical Methods in Computer Science, 8(4), pages 1-44, 2012.
Special issue for selected papers from CSL'10. 

11. André Platzer.
[Dynamic logics of dynamical systems](http://arxiv.org/abs/1205.4788).
May 2012.
arXiv:1205.4788

Copyright and Licenses
======================

Copyright (C) 2014-2017 Carnegie Mellon University. See COPYRIGHT.txt for details.
Developed by Andre Platzer, Stefan Mitsch, Nathan Fulton, Brandon Bohrer, Jan-David Quesel, Yong Kiam Tan, Marcus Voelp, Ran Ji.

See LICENSE.txt for the conditions of using this software.

The KeYmaera X distribution contains external tools. A list of tools and their licenses can be found in

    keymaerax-webui/src/main/resources/license/tools_licenses

Background & References
=======================

Background material and more material can be found at

http://keymaeraX.org/

http://www.ls.cs.cmu.edu/publications.html

Contact
=======

KeYmaera X developers: keymaeraX@keymaeraX.org
