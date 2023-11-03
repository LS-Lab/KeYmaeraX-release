KeYmaera X Theorem Prover for Hybrid Systems
============================================

Self-driving cars, autonomous robots, modern airplanes, or robotic surgery: we increasingly entrust our lives to computers and therefore should strive for nothing but the highest safety standards - mathematical correctness proof. Proofs for such cyber-physical systems can be constructed with the KeYmaera X prover. As a _hybrid systems_ theorem prover, KeYmaera X analyzes the control program and the physical behavior of the controlled system together in _differential dynamic logic_.

KeYmaera X features a minimal core of just about 2000 lines of code that isolates all soundness-critical reasoning. Such a small and simple prover core makes it much easier to trust verification results. Pre-defined and custom tactics built on top of the core drive automated proof search. KeYmaera X comes with a web-based front-end that provides a clean interface for both interactive and automated proving, highlighting the most crucial parts of a verification activity. Besides hybrid systems, KeYmaera X also supports the verification of _hybrid games_ in _differential game logic_.

**More information** and precompiled binaries are available at:
  https://keymaeraX.org/

* [KeYmaera X Tutorial](https://keymaeraX.org/Xtutorial.html)
* [KeYmaera X Releases](https://github.com/LS-Lab/KeYmaeraX-release/releases)
* [Logical Foundations of Cyber-Physical Systems](http://lfcps.org/lfcps/) textbook
* [KeYmaera X API Documentation](https://keymaerax.org/scaladoc)

Installation
============
The easiest way to run KeYmaera X is to download binaries 
[keymaerax.jar](https://keymaeraX.org/keymaerax.jar) and start from command line:

    java -jar keymaerax.jar

For this to succeed, ensure that the following software is installed:
- [Oracle Java Development Kit JDK/Java Runtime Environment JRE](https://www.oracle.com/java/technologies/javase-downloads.html) or [OpenJDK/JRE](https://openjdk.java.net/)
  (version 1.8 or later, tested up to Java 15)
- Use any number of the following real arithmetic solvers:
  - [Wolfram Mathematica](https://www.wolfram.com/mathematica/)
    (version 10+ recommended. Previous versions may work but are only compatible with Java 1.6 and 1.7.
    The Mathematica J/Link library that comes with Mathematica is needed during compilation. Mathematica needs to be activated to use it also at runtime.
    Without active Mathematica, the [Z3 Solver](https://github.com/Z3Prover/z3) is automatically used for real arithmetic.)
  - [Wolfram Engine](http://www.wolfram.com/engine)
    free alternative to Wolfram Mathematica that needs an active internet connection.
  - [Z3 Solver](http://www.wolfram.com/engine)
    comes built-in without installation but still provides less functionality.

See [more details on installation, usage, FAQ](https://keymaeraX.org/download.html)

#### Configuration
KeYmaera X requires a decision procedure for real arithmetic to finalize proofs. It is tested best with Mathematica and some features are only available when using Mathematica.
After starting KeYmaera X you can configure arithmetic tools in the _KeYmaera X->Preferences_ menu.

Depending on the operating system, Mathematica is installed in different locations. 
Alternatively, you can also specify which arithmetic tools to use from command line with
parameters `-mathkernel` and `-jlink`. Example parameters that are appropriate when
Mathematica is installed in the default location are provided below.

#### Default Configuration Parameters per Operating System
macOS, 64bit, Mathematica 10.4+
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

To compile KeYmaera X from source, see the [build instructions](doc/build.md).
To set up a development environment, see the [dev instructions](doc/develop.md).

More detailed but outdated instructions are available [in the wiki on GitHub](https://github.com/LS-Lab/KeYmaeraX-release/wiki/Building-Instructions).

Publications
============

KeYmaera X implements the uniform substitution calculus for differential dynamic logic in order to enable soundness assurance by way of a small trusted LCF-style kernel while still being amenable to automatic theorem proving.

https://www.ls.cs.cmu.edu/publications.html

1. André Platzer. 
[A complete uniform substitution calculus for differential dynamic logic](https://doi.org/10.1007/s10817-016-9385-1).
Journal of Automated Reasoning 59(2), pp. 219-266, 2017.
Extended version of [CADE-25](https://doi.org/10.1007/978-3-319-21401-6_32).

2. André Platzer.
[Logics of dynamical systems](https://doi.org/10.1109/LICS.2012.13).
ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012.

3. Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Völp and André Platzer. 
[KeYmaera X: An axiomatic tactical theorem prover for hybrid systems](https://doi.org/10.1007/978-3-319-21401-6_36).
In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE-25, Berlin, Germany, Proceedings, LNCS. Springer, 2015. 

4. Nathan Fulton, Stefan Mitsch, Brandon Bohrer and André Platzer. 
[Bellerophon: Tactical theorem proving for hybrid systems](https://doi.org/10.1007/978-3-319-66107-0_14).
In Mauricio Ayala-Rincón and César Muñoz, editors, Interactive Theorem Proving, International Conference, ITP 2017, volume 10499 of LNCS, pp. 207-224. Springer, 2017. 

5. André Platzer.
[Logical Foundations of Cyber-Physical Systems](http://lfcps.org/lfcps/).
Springer, Cham, 2018. [DOI](https://doi.org/10.1007/978-3-319-63588-0), [Videos](http://video.lfcps.org/)

The soundness assurances provided by a small LCF-style kernel are further strengthened by a cross-verification of the soundness theorem for the uniform substitution calculus.

6. Brandon Bohrer, Vincent Rahli, Ivana Vukotic, Marcus Völp and André Platzer.
[Formally verified differential dynamic logic](https://doi.org/10.1145/3018610.3018616).
ACM SIGPLAN Conference on Certified Programs and Proofs, CPP 2017, Jan 16-17, 2017, Paris, France, pages 208-221, ACM, 2017.
[Isabelle/HOL](https://github.com/LS-Lab/Isabelle-dL) and [Coq](https://github.com/LS-Lab/Coq-dL)

A secondary goal of KeYmaera X is to also make it possible to implement extensions of differential dynamic logic, such as differential game logic for hybrid games as well as quantified differential dynamic logic for distributed hybrid systems:

7. André Platzer. 
[Differential game logic](https://doi.org/10.1145/2817824).
ACM Trans. Comput. Log. 17(1), 2015.

8. André Platzer. 
[Differential hybrid games](https://doi.org/10.1145/3091123).
ACM Trans. Comput. Log. 18(3), 2017.

9. André Platzer.
[A complete axiomatization of quantified differential dynamic logic for distributed hybrid systems](https://doi.org/10.2168/LMCS-8(4:17)2012).
Logical Methods in Computer Science 8(4), pages 1-44, 2012.

KeYmaera X implements fast generalized uniform substitution algorithms, also cross-verified:

10. André Platzer.
[Uniform substitution for differential game logic](https://doi.org/10.1007/978-3-319-94205-6_15).
In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.

11. André Platzer.
[Uniform substitution at one fell swoop](https://doi.org/10.1007/978-3-030-29436-6_25).
In Pascal Fontaine, editor, International Conference on Automated Deduction, CADE-27, volume 11716 of LNCS, pp. 425-441. Springer, 2019.
[Isabelle/HOL](http://isa-afp.org/entries/Differential_Game_Logic.html)

Automatic proofs for differential equation invariants are based on:

12. André Platzer and Yong Kiam Tan. 
[Differential equation invariance axiomatization](https://doi.org/10.1145/3380825). 
J. ACM 67(1), 6:1-6:66, 2020. 
Extended version of [LICS'18](https://doi.org/10.1145/3209108.3209147). 

Liveness proofs for differential equations are based on:

13. Yong Kiam Tan and André Platzer.
Yong Kiam Tan and André Platzer. 
[An axiomatic approach to existence and liveness for differential equations](https://doi.org/10.1007/s00165-020-00525-0). 
Formal Aspects of Computing 33(4), pp 461-518, 2021.
Special issue for selected papers from [FM'19](https://doi.org/10.1007/978-3-030-30942-8_23). 

KeYmaera X uses the [Pegasus](http://pegasus.keymaeraX.org/) tool for invariant generation (which gets better when additional software is installed):

14. Andrew Sogokon, Stefan Mitsch, Yong Kiam Tan, Katherine Cordwell and André Platzer. 
[Pegasus: Sound continuous invariant generation](https://doi.org/10.1007/s10703-020-00355-z).
Formal Methods in System Design, 58(1), pp. 5-41, 2022. 
Special issue for selected papers from [FM'19](https://doi.org/10.1007/978-3-030-30942-8_10).

KeYmaera X implements the [ModelPlex](http://modelplex.net) method to ensure that verification results about models apply to cyber-physical system implementations. ModelPlex generates provably correct monitor conditions that, if checked to hold at runtime, are provably guaranteed to imply that the offline safety verification results about the CPS model apply to the present run of the actual CPS implementation.

15. Stefan Mitsch and André Platzer. 
[ModelPlex: Verified runtime validation of verified cyber-physical system models](https://doi.org/10.1007/s10703-016-0241-z). 
Formal Methods in System Design 49(1), pp. 33-74. 2016. 
Special issue for selected papers from [RV'14](https://doi.org/10.1007/978-3-319-11164-3_17).

16. Yong Kiam Tan, Stefan Mitsch and André Platzer.
[Verifying switched system stability with logic](https://doi.org/10.1145/3501710.3519541)
In Ezio Bartocci and Sylvie Putot, editors, Hybrid Systems: Computation and Control (part of CPS Week 2022), HSCC'22. Article No. 2, pp. 1-11. ACM, 2022.

The design principles for the user interface of KeYmaera X are described in:

17. Stefan Mitsch and André Platzer. 
[The KeYmaera X proof IDE: Concepts on usability in hybrid systems theorem proving](https://doi.org/10.4204/EPTCS.240.5). 
In Catherine Dubois, Paolo Masci and Dominique Méry, editors, 3rd Workshop on Formal Integrated Development Environment F-IDE 2016, volume 240 of EPTCS, pp. 67-81, 2017.

Model and proof management techniques are described in:

18. Stefan Mitsch.
[Implicit and Explicit Proof Management in KeYmaera X](https://doi.org/10.4204/EPTCS.338.8)
In José Proença and Andrei Paskevich, editors, 6th Workshop on Formal Integrated Development Environment F-IDE 2021, volume 338 of EPTCS 338, pp. 53-67, 2021.

A comparison of KeYmaera X with its predecessor provers is described in:

19. Stefan Mitsch and André Platzer. 
[A Retrospective on Developing Hybrid System Provers in the KeYmaera Family: A Tale of Three Provers](https://doi.org/10.1007/978-3-030-64354-6_2). 
In Wolfgang Ahrendt et al., editors, Deductive Software Verification: Future Perspectives, volume 12345 of LNCS, pp. 21-64. Springer, 2020

Copyright and Licenses
======================

Copyright (C) 2014-2022 Carnegie Mellon University. See COPYRIGHT.txt for details.
Developed by Andre Platzer, Stefan Mitsch, Nathan Fulton, Brandon Bohrer, Jan-David Quesel, Yong Kiam Tan, Andrew Sogokon, Fabian Immler, Marcus Voelp, Ran Ji.

See LICENSE.txt for the conditions of using this software.

The KeYmaera X distribution contains external tools. A list of tools and their licenses can be found in

    keymaerax-webui/src/main/resources/license/tools_licenses

Contact
=======

KeYmaera X developers: keymaeraX@keymaeraX.org
