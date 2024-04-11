# Architecture

This file documents the high-level architecture and project structure of KeYmaera X.
It serves as an introduction to the code base for developers and maintainers.

See the blog post [ARCHITECTURE.md](https://matklad.github.io/2021/02/06/ARCHITECTURE.md.html)
for more details on this kind of documentation.

## Basic structure

As a theorem prover, KeYmaera X puts importance on correctness.
This means that bugs should not be soundness critical in most parts of the code base.
In other words, bugs should not be able to cause incorrect statements to be proven true.
The project is split into three main parts:

1. **The kernel.**
   The kernel is a small set of files (under 3000 sloc) that implement the soundness critical parts of proof checking.
   Its main jobs are defining the data types for logical expressions and proofs
   as well as a few fundamental operations, the most important of which is uniform substitution.

2. **The core.**
   The core builds infrastructure around the kernel to make it actually useful.
   It includes parsing and formatting, configuration, caching of partial results,
   and managing of external tools for deciding real arithmetic.
   Most importantly, the core contains **Bellerophon**, a tactics language for proof search,
   as well as a large library of tactics, proof rules and derived axioms (pre-proven statements).

3. **The web UI.**
   To provide its UI, KeYmaera X runs a web server (usually locally) that users connect to with their browsers.
   This is how most users of KeYmaera X will interact with it.

To ensure that bugs in other parts of the code base do not affect the soundness,
the kernel employs a type called `Provable` to represent statements or proof steps that were proven valid.
Only the kernel can construct instances of this type, and the kernel only constructs valid instances.
Code (including kernel code) may rely on any `Provable` instance being valid
as it must have come from the kernel (barring tricks like reflection).
There exists an escape hatch for external tools for deciding real arithmetic.

When proving a theorem, the theorem is first parsed.
If provided, a proof written in the Bellerophon tactics language is also parsed.
The proof may also be interactively entered via the web UI.
The tactics are then applied by a Bellerophon interpreter to construct a proof tree.
In the end, the proof tree is collapsed to a single `Provable` as a final check for correctness.
Only then is the theorem considered proven

### Kernel code style

The kernel avoids the more advanced features of the Scala language.
This has two reasons:

First, since the kernel is soundness-critical, it should be simple and easy to understand.
In order to trust proofs accepted by KeYmaera X, the kernel must be bug-free.
Avoiding complex language features makes the code easier to reason about, even for non-Scala developers.

Second, it makes it easier to port the kernel to other languages.
By avoiding more advanced language features and focusing on a subset common to many object-oriented languages,
fewer tweaks are required to adapt to a new language.

## Code map

This section gives an overview of the structure of files in the repository.

### `.github/`

Config for [GitHub Actions](https://docs.github.com/en/actions)-based CI.

Since building the project requires an instance of Mathematica's `JLink.jar` at compile-time,
the custom action `.github/actions/obtain-jlink-jar/` obtains one
from the publicly available [Wolfram Engine](https://docs.github.com/en/actions) docker image.

### `.idea/`, `.scalafmt.conf`

IDE and tooling config.
Only [IntelliJ IDEA](https://www.jetbrains.com/idea/) is officially supported.

### `build.sbt`, `project/`

KeYmaera X uses [sbt](https://www.scala-sbt.org/) for project setup and building.
These files contain the sbt project configuration.

### `doc/`

Documentation in the form of markdown files.

### `keymaerax-core/`

This subproject contains the soundness-critical kernel as well as the core.

The kernel is located in the `edu.cmu.cs.ls.keymaerax.core` package.
Infrastructure around the kernel that is not soundness-critical can be found in `edu.cmu.cs.ls.keymaerax.infrastruct`.
Integration with external tools like Mathematica and Z3 happens in `edu.cmu.cs.ls.keymaerax.tools`.

The Bellerophon language and interpreter are at `edu.cmu.cs.ls.keymaerax.bellerophon`
while the tactic library is at `edu.cmu.cs.ls.keymaerax.btactics`.
While tactics are scattered all throughout the package and its subpackages,
proof rules and derived axioms are exclusively located in `edu.cmu.cs.ls.keymaerax.btactics.Ax`.

### `keymaerax-webui/`

This subproject contains the web server and web UI.

The web server and web API implementation named **Hydra**
is located in the `edu.cmu.cs.ls.keymaerax.hydra` package and subpackages.
The HTML, CSS, JS files as well as all JS dependencies and other assets can be found in the project resources.

The subproject also contains a launcher in the `edu.cmu.cs.ls.keymaerax.launcher` package
that restarts the jar on startup with a JVM option for more stack space.

Finally, the subproject contains tests for both itself and the `keymaerax-core/` subproject.

### `keymaerax-js/`

The web UI sometimes needs to parse expressions, for example for syntax highlighting when editing.
[Scala.js](https://www.scala-js.org/) is used to transpile the parsers from the core to JavaScript.

This subdirectory is an entirely separate sbt project with its own `build.sbt` and `project/` directory.
The build config manually includes some files from `keymaerax-core/`.
Some of the source files are automatically generated.

### `keymaerax-macros/`

KeYmaera X uses macros to annotate tactics, proof rules, and derived axioms with metadata.
The macros are also used for detecting available tactics on startup.
Finally, they modify the implementation of annotated definitions for technical reasons.

Scala 3 changed its macro system in a backwards-incompatible way.
Currently, the reliance on Scala 2 macros is one of the factors preventing a migration to Scala 3.
Efforts are underway to get rid of all custom macros to make migration easier.

## Cross-cutting concerns

This section talks about design decisions that are not linked to a particular place in the code.

### Code generation

At the moment, some code files are generated, not manually written.
The process to generate the files is manual and differs from file to file.
A non-exhaustive list of such files:

- `keymaerax-js/src/main/scala/edu/cmu/cs/ls/keymaerax/btactics/macros/DerivationInfo.scala`
- `keymaerax-webui/src/main/resources/keymaerax.sqlite`
- `keymaerax-webui/src/main/scala/edu/cmu/cs/ls/keymaerax/hydra/Tables.scala`
- Parts of `keymaerax-webui/src/main/resources/js/ace/src-min-noconflict/worker-bellerophon.js`
- Parts of `keymaerax-webui/src/main/resources/js/ace/src-min-noconflict/worker-dl.js`
