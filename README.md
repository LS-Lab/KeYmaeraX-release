KeYmaera X
==========

Self-driving cars, autonomous robots, modern airplanes, or robotic surgery: we increasingly entrust our lives to computers and therefore should strive for nothing but the highest safety standards - mathematical correctness proof. Proofs for such cyber-physical systems can be constructed with the KeYmaera X prover. As a hybrid systems theorem prover, KeYmaera X analyzes the control program and the physical behavior of the controlled system together in differential dynamic logic.

KeYmaera X features a minimal core of just 1700 lines of code that isolates all soundness-critical reasoning. Such a small and simple prover core makes it much easier to trust verification results. Pre-defined and custom tactics built on top of the core drive automated proof search. KeYmaera X comes with a web-based front-end that provides a clean interface for both interactive and automated proving, highlighting the most crucial parts of a verification activity.

More information and precompiled binaries are available at:
  http://keymaeraX.org/

Installation
============
The easiest way to run KeYmaera X is to download binaries 
[keymaerax.jar](http://keymaerax.org/keymaerax.jar) and run via

    java -jar keymaerax.jar

First ensure that the following software is installed
- [Java Development Kit JDK](https://java.com/download)
  (version 1.8+ recommended. Mathematica 9.0 is only compatible with Java 1.6 and 1.7. Mathematica 10.0+ are also compatible with Java 1.8)
- [Wolfram Mathematica](https://www.wolfram.com/mathematica/)
  (version 10+ recommended. Other versions may work.
  The Mathematica J/Link library that comes with Mathematica is needed during compilation. Mathematica needs to be activated to use it also at runtime.
  Otherwise the [Z3 Solver](https://github.com/Z3Prover/z3) is automatically used for real arithmetic.)

#### FAQ: Run Problems

If running `java -jar keymaerax.jar` results in the error `Invalid or corrupt jarfile` then update to Java 1.8 and to Mathematic 10+.
If you need to use an earlier version of Java or Mathematica, you can also run KeYmaera X via

    java -Xss20M -cp keymaerax.jar KeYmaeraX

If KeYmaera X acts weird after an update, clean your local cache of lemmas by removing (or renaming) the directory `~/.keymaerax/cache`.
You could also try renaming the model and proof database `~/.keymaerax/keymaerax.sqlite` (if this file has become corrupt, it may prevent KeYmaera X from working properly).

Errors related to JLinkNative Library are caused by incompatibilities of Java 1.8 in combination with Mathematica 9. It is recommended to use Mathematica 10. Or they may be caused by some operating system configuration issues.

#### Configuration
KeYmaera X requires a decision procedure for real arithmetic to finalize proofs. It is tested best with Mathematica.
Depending on the operating system, Mathematica is installed in different locations. Adapt prove.sh to specify the
parameters -mathkernel and -jlink according to the local Mathematica setup. Parameters that are appropriate when
Mathematica is installed in the default location are provided below.

#### Default Configuration Parameters per Operating System
MacOS, 64bit, Mathematica 10.4+
* `-mathkernel /Applications/Mathematica.app/Contents/MacOS/MathKernel`
* `-jlink /Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64`

Linux, 64bit, Mathematica 10.4+
* `-mathkernel /usr/local/Wolfram/Mathematica/10.4/Executables/MathKernel`
* `-jlink /usr/local/Wolfram/Mathematica/10.4/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64`

Windows, 64bit, Mathematica 10.4+
* `-mathkernel "C:\Program Files\Wolfram Research\Mathematica\10.4\MathKernel.exe"`
* `-jlink "C:\Program Files\Wolfram Research\Mathematica\10.4\SystemFiles\Links\JLink\SystemFiles\Libraries\Windows-x86-64"`

Building
========
To compile KeYmaera X from source code, see [Building Instructions](https://github.com/LS-Lab/KeYmaeraX-release/wiki/Building-Instructions)


Specification
=============

KeYmaera X implements the uniform substitution calculus for differential dynamic logic in order to enable soundness assurance by way of a small trusted LCF-style kernel while still being amenable to automatic theorem proving.

1. André Platzer. 
[A complete uniform substitution calculus for differential dynamic logic](http://dx.doi.org/10.1007/s10817-016-9385-1). 
Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
* Based on: André Platzer. 
[A uniform substitution calculus for differential dynamic logic](http://dx.doi.org/10.1007/978-3-319-21401-6_32). 
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.

2. André Platzer.
[Logics of dynamical systems](http://dx.doi.org/10.1109/LICS.2012.13).
ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012.

3. Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Völp and André Platzer. 
[KeYmaera X: An axiomatic tactical theorem prover for hybrid systems](http://dx.doi.org/10.1007/978-3-319-21401-6_36). 
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. 

4. Nathan Fulton, Stefan Mitsch, Brandon Bohrer and André Platzer. 
[Bellerophon: Tactical theorem proving for hybrid systems](http://dx.doi.org/10.1007/978-3-319-66107-0_14). 
In Mauricio Ayala-Rincón and César Muñoz, editors, Interactive Theorem Proving, International Conference, ITP 2017, volume 10499 of LNCS. Springer, 2017. 

5. André Platzer.
[Logical Foundations of Cyber-Physical Systems](http://lfcps.org/lfcps/).
Springer, 2017. 


Further background information can be found in:

6. André Platzer.
[Differential dynamic logic for hybrid systems](http://dx.doi.org/10.1007/s10817-008-9103-8).
Journal of Automated Reasoning, 41(2), pages 143-189, 2008.

7. André Platzer.
[Logical Analysis of Hybrid Systems: Proving Theorems for Complex Dynamics](http://dx.doi.org/10.1007/978-3-642-14509-4).
Springer, 2010. ISBN 978-3-642-14508-7. 

8. André Platzer.
[The structure of differential invariants and differential cut elimination](http://dx.doi.org/10.2168/LMCS-8(4:16)2012).
Logical Methods in Computer Science, 8(4), pages 1-38, 2012. 

A secondary goal of KeYmaera X is to also make it possible to implement extensions of differential dynamic logic, such as differential game logic for hybrid games as well as quantified differential dynamic logic for distributed hybrid systems:

9. André Platzer. 
[Differential game logic](http://dx.doi.org/10.1145/2817824). 
ACM Trans. Comput. Log., 17(1), 2015.

10. André Platzer. 
[Differential hybrid games](http://dx.doi.org/10.1145/3091123). 
ACM Trans. Comput. Log., 18(3), 2017.

11. André Platzer.
[A complete axiomatization of quantified differential dynamic logic for distributed hybrid systems](http://dx.doi.org/10.2168/LMCS-8(4:17)2012).
Logical Methods in Computer Science, 8(4), pages 1-44, 2012.

12. André Platzer.
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

Publications & References
=======================

Publications and more material can be found at

http://keymaeraX.org/

http://www.ls.cs.cmu.edu/publications.html

Contact
=======

KeYmaera X developers: keymaeraX@keymaeraX.org
