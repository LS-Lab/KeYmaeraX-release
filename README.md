KeYmaera X
==========

KeYmaera X is a theorem prover for differential dynamic logic (dL), a logic for specifying and verifying properties of hybrid systems with mixed discrete and continuous dynamics. Reasoning about complicated hybrid systems requires support for sophisticated proof techniques, efficient computation, and a user interface that crystallizes salient properties of the system. KeYmaera X allows users to specify custom proof search techniques as tactics, execute tactics in parallel, and interface with partial proofs via an extensible user interface.

KeYmaera X is built up from a small trusted core. The core contains a finite list of locally sound dL axioms that are instantiated using a uniform substitution proof rule. Isolating all soundness-critical reasoning in this axiomatic core obviates the otherwise intractable task of ensuring that proof search algorithms are implemented correctly. This enables advanced proof search features---such as aggressive, speculative proof search and user-defined tactics built using a flexible tactic language---without correctness concerns that could undermine the usefulness of automated analysis. Early experimentation with KeYmaera X suggests that a single layer of tactics on top of the axiomatic core provides a rich language for implementing novel and highly sophisticated automatic proof procedures.

  http://keymaeraX.org/

Installation
============

The easiest way to run KeYmaera X from source is to install its dependencies and run HyDRA via SBT:

    * Install Scala (and the JRE).
    * Install SBT and following the instructions in the Building section.

Building
========

We use the Scala Build Tool (sbt). Installation instructions are available
at the link following:

http://www.scala-sbt.org/release/docs/Getting-Started/Setup.html

Detailed instructions are available at that website as well. Briefly, type

    sbt compile

to compile the source code. First-time compilation may take a while, since it downloads all necessary libraries,
including Scala itself. The build file includes paths to the Mathematica JLink jar, for example for Mac as follows.

    unmanagedJars in Compile += file("/Applications/Mathematica.app/SystemFiles/Links/JLink/JLink.jar")

If JLink.jar is in a non-default location on your computer, add a new line to build.sbt.

Type

    sbt test

to run the regression test case suite.
If you run into problems during the compilation process, use "sbt clean" for a fresh start to remove stale files.

The Wiki contains extended build instructions and solutions to other
common sbt problems:

https://github.com/LS-Lab/KeYmaera4/wiki/Building-Instructions

Generating Scaladoc
===================

To generate Scaladoc documentation files, run:

    sbt doc

Documentation will be generated for each subproject in the 
`target/scala-x.xx/api` directory of the subproject. 
For instance, `keymaerax-core/target/scala-2.10/api` for the core subproject.

To generate unified scaladoc for all subprojects, run:

    sbt unidoc


IntelliJ IDEA
=============

If you want to use the IntelliJ IDEA development environment, install it:
- Install IntelliJ IDEA
- Install the Scala plugin

Project Setup
- Create a new Scala project, backed by SBT
- Select a JDK as your project SDK, add a new one if not previously added
- Check `update automatically` (not checked by default), so that updates to build.sbt are reflected automatically in the project

Create a new run configuration of type Application.
- Main class: `edu.cmu.cs.ls.keymaerax.hydra.Boot`
- Set the working directory to the project path
- Use the classpath of your project module

Front End
=========

    sbt "~ re-start"
    open http://localhost:8090/index_bootstrap.html

The option re-start ensures that the server is automatically restarted whenever a source file changes.

Errors related to JLinkNative Library are caused by Java 1.8 in combination with Mathematica 9.
Either run using Java 1.7, or update to Mathematica 10.

KeYmaera X is successfully started when you see the following console output

    Bound to localhost/127.0.0.1:8090

Source Code Layout
==================

build.sbt - SBT configuration file

keymaerax-core/src/ - Source code directory

keymaerax-core/src/main/scala - source code (edu.cmu.cs.ls.keymaerax)

Within the edu.cmu.cs.ls.keymaerax namespace, code is separated according to functionality:

    .core    - Soundness-critical core
    .parser  - Parsing and pretty printing
    .tactics - Tactic framework, including tactic implementations and the scheduler
    .tools   - Arithmetic back-ends

keymaerax-webui/src/ - Source code directory for Web UI etc.

keymaerax-webui/src/test/scala - tests run by `sbt test`

The wiki contains an introduction to the testing framework:
https://github.com/LS-Lab/KeYmaera4/wiki/How-to-Add-Tests
http://www.scalatest.org/user_guide

target/ - Generated files directory created by sbt on first compilation.

target/scala-2.10/classes/ - Target directory for sbt compilation.

Test Cases
==========

The full test suite can be run by

    sbt test

Selectively running individual test cases within sbt:

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

Optional Database Alternative: MongoDB
=============================

If you prefer to work with a MongoDB than with SQL you also need to install

    * Install MongoDB. Be sure that that your machine is behind a firewall and/or edit the MongoDB configuration file so that the server binds to the loopback address.

Make sure to run the following before starting KeYmaera X:

    mongod --config /usr/local/etc/mongod.conf

Specification
=============

The goal of KeYmaera X is to implement the proof calculus of differential dynamic logic in a way that is amenable to soundness ensurance by way of a small trusted LCF-style core while still being amenable to automatic theorem proving.
Differential dynamic logic and its Hilbert-type and sequent proof calculi have been described and specified in more detail in:

André Platzer. 
A uniform substitution calculus for differential dynamic logic. 
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.

André Platzer. 
A uniform substitution calculus for differential dynamic logic. 
arXiv 1503.01981.

André Platzer.
Logics of dynamical systems.
ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012.

André Platzer.
Differential dynamic logic for hybrid systems.
Journal of Automated Reasoning, 41(2), pages 143-189, 2008.

André Platzer.
Logical Analysis of Hybrid Systems: Proving Theorems for Complex Dynamics.
Springer, 2010. 426 p. ISBN 978-3-642-14508-7. 

André Platzer.
Differential dynamic logic for verifying parametric hybrid systems.
In Nicola Olivetti, editor, Automated Reasoning with Analytic Tableaux and Related Methods, International Conference, TABLEAUX 2007, Aix en Provence, France, July 3-6, 2007, Proceedings, volume 4548 of LNCS, pages 216-232. Springer, 2007. 

The prover is described in

Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Völp and André Platzer. 
KeYmaera X: An axiomatic tactical theorem prover for hybrid systems. 
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. 

The advanced proof techniques of differential invariants, differential cuts, and differential ghosts are described and specified in

André Platzer.
The structure of differential invariants and differential cut elimination.
Logical Methods in Computer Science, 8(4), pages 1-38, 2012. 

A secondary goal of KeYmaera X is to also make it possible to implement extensions of differential dynamic logic, such as quantified differential dynamic logic, which, along with its proof calculus, has been described and specified in

André Platzer.
A complete axiomatization of quantified differential dynamic logic for distributed hybrid systems.
Logical Methods in Computer Science, 8(4), pages 1-44, 2012.
Special issue for selected papers from CSL'10. 

André Platzer.
Dynamic logics of dynamical systems.
May 2012.
arXiv:1205.4788

André Platzer. 
Differential game logic. 
August 2014.
arXiv:1408.1980

Jan-David Quesel and André Platzer.
Playing hybrid games with KeYmaera.
In Bernhard Gramlich, Dale Miller, and Ulrike Sattler, editors, Automated Reasoning, Sixth International Joint Conference, IJCAR 2012, Manchester, UK, Proceedings, volume 7364 of LNCS, pages 439-453. Springer, June 2012

Licenses of External Tools
==========================

KeYmaera X distribution contains external tools. A list of tools and their licenses can be found at

src/main/resources/license/tools_licenses

Background & References
=======================

Background material and more material can be found at

http://symbolaris.com/pub/

http://symbolaris.com/info/KeYmaera.html

