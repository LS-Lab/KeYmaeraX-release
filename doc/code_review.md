# KeYmaera X Kernel Code Review

1. The primary purpose of the code review is to check and establish correctness of all soundness-critical parts of the
   KeYmaera X theorem prover.

2. The secondary purpose of the review is to identify whether there are better ways of implementing KeYmaera X, but
   precedence will be given to purpose 1). Except for minor edits, those improvements will not be performed during the
   code review but noted for later inplace with `TODO` or in a separate file.

During the KeYmaera X Kernel Code Review, the whole source code of the relevant packages will be reviewed for
correctness and compliance with the theoretical results. We follow the principle of Cartesian Doubt and scrutinize the
code until everybody present is convinced that the code is correct. The code review cannot proceed to other parts of the
code until everybody has established its correctness. If anyone present during a kernel code review has any doubt about
any part of the code, pertaining to its correctness, the code review cannot move on until the doubt has been settled or
a flag has been placed along with an explanation:

```scala
// TODO Code Review: indication of concern or reason or agenda
```

The code review will only proceed successfully if everybody present clearly and independently stated that he is
convinced that the code is correct.

Please don't hesitate at all if some part of the code is unclear to you! It is the purpose of the code review to clarify
what the KeYmaera X Kernel does and whether it is correctly doing what it should be doing. Confusion about the code are
likely sources of trouble. And simpler code is much easier to get sound than complex contraptions. So it is crucial for
the KeYmaera X project to point out possible sources of deficiencies or ambiguities or subtle nuances.

Follow-up: when resolving or addressing all important @todo comments introduced during a Code Review, the git commit
messages should identify the issue that they are addressing explicitly. And a corresponding Delta Review needs to be
initiated to confirm resolution of the matter. A record of the resolution of the @todo messages should be left
explicitly.

## KeYmaera X Kernel Code Review Steps

1. `Expression.scala` for correctness and compliance with section 2.1 \[1\]
2. `StaticSemantics.scala` for correctness and compliance with section 2.4 \[1\]
3. `UniformSubstitution.scala` for correctness and compliance with section 3.0 \[1\], (yet USubstChurch unused)
4. `USubstOne.scala` for correctness and compliance with section 3.0 \[4\]
5. `UniformRenaming.scala` for correctness
6. `Proof.scala` for correctness and compliance with \[1\] as well as sequent calculus \[2\]
7. `AxiomBase.scala` for correctness and compliance with Fig 2+3 \[1\] or hybrid games \[3,4\]
8. `SetLattice.scala` for correctness,
   and `Errors.scala`, `PrettyPrinter.scala`, `QETool.scala`, `Lemma.scala`, `Assertion.java`, `package.scala`

If you are convinced of the correct implementation of the KeYmaera X Kernel you will indicate so by verbal agreement and
by signing the same commit with your secret GPG key to which only you have access. We will also be placing a tag to
clearly mark the reviewed version of the code.

Changes to the KeYmaera X Kernel need to be reviewed periodically in similar ways. Regular full core reviews are
advised. Smaller changes will review only the differences formally (Delta Review) or informally (unmarked).

If there are any questions about the KeYmaera X Kernel code review or any suggestions on how it could be improved,
please ask! Questions and clarifications are good!

**Extended Code Review:**
In addition to the above files, an extended code review also considers

1. parser package:
   `PrettyPrinter.scala`, `KeYmaeraXPrettyPrinter.scala`, `OpSpec.scala`
2. lemma package:
   `LemmaDB.scala`, `LemmaDBFactory.scala`, `LemmaDBBase.scala`, `FileLemmaDB.scala`, `CachedLemmaDB.scala`
3. tools.qe package:
   `SMTConverter.scala`, `Z3*.scala`, `KeYmaeraToMathematica.scala`, `Mathematica*.scala`, `BigDecimalQETool.scala`

## References

1. André Platzer.
   A complete uniform substitution calculus for differential dynamic logic.
   Journal of Automated Reasoning, 59(2), pp. 219-265, 2017.
   [DOI 10.1007/s10817-016-9385-1](https://doi.org/10.1007/s10817-016-9385-1)

   André Platzer.
   A uniform substitution calculus for differential dynamic logic.
   In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
   Germany, Proceedings, volume 9195 of LNCS, pages 467-481. Springer, 2015.
   [arXiv 1503.01981](http://arxiv.org/abs/1503.01981)

2. André Platzer.
   Differential dynamic logic for hybrid systems.
   Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
   [DOI 10.1007/s10817-008-9103-8](https://doi.org/10.1007/s10817-008-9103-8)

3. André Platzer.
   Differential game logic.
   ACM Trans. Comput. Log., 17(1), pages 1:1-1:52, 2015.
   [DOI 10.1145/2817824](https://doi.org/10.1145/2817824)

4. André Platzer.
   Uniform substitution at one fell swoop.
   In Pascal Fontaine, editor, International Conference on Automated Deduction, CADE'19, Natal, Brazil, Proceedings,
   volume 11716 of LNCS, pp. 425-441. Springer, 2019.
   [DOI 10.1007/978-3-030-29436-6_25](https://doi.org/10.1007/978-3-030-29436-6_25)

## Code Review Log

The date of last full code review is added to the top of the file as `// Code Review: 2020-02-17`.
A log of all major code reviews and the findings are reported here:

### Code Review: KeYmaera X Core: 2020-02-17

* Verdict: stable
* DI: system generalization can only have bound variables of the ODE free in postcondition (and no resulting `''` by
  data structure invariant), just like DI itself has `p(x)`. Vectorial DI systems.
* RI, DX skip: no `'` in postcondition (no bound differential symbols). Vectors suffice to
  say `[X'=f(X)&q(X)]p(X) -> (q(X)->p(X))`
* VDG: vectorial DG with vectorial quantifier for liveness.
* DG: singularities from division by zero disallowed, also via interpreted functions.

Code Review confirmed

* DONE con: program needs `SpaceDependent(Except(v))`.
* DONE VDG: vectorial DG with vectorial quantifier. DONE indirectly by DG-based differential invariance tactic.
* DONE Barcan axiom: could add if SystemConst became SpaceDependent.

### Code Review: KeYmaera X Core: 2016-08-17

* Verdict: stable
* NOTE Could turn `DifferentialProgram` into non-Program.
* NOTE Could remove some convenience functionality from the core that the core does not use.

### Extended Delta Code Review: 2016-08-16 Full review of lemma handling

* NOTE Lemma could isolate checksum handling exclusively into toString and fromString
* TODO Review `SQLLite.getLemmas` and its interaction with create and contracts.
* TODO Number format standard in SMTLIB seems underdefined.
* TODO Polya result parsing needs to become more reliable

### Extended Code Review: 2016-08-02 but not core code review

* Verdict: Significant improvement of reliability of tool handling.
* TODO Add lemma evidence directly in `LemmaDB.toString`
* TODO Could refactor lemmadb to have a single caching layer and just separate storage layers.
* TODO Remove Projection from data structures and turn them into an axiomatic treatment.
* TODO Mathematica conversion needs separate Forall,Exists because of Scala
* TODO Check number format standard in SMTLIB
* TODO Polya result parsing needs to become more reliable

### Extended Code Review: KeYmaera X Core: 2016-06-01

* TODO Clean handling of assumptions about interpreted functions. For example unproved premises that are substituted in
  with *formula* definitions in the end.
* TODO FileLemmaDB needs to check all evidence not just the first.

* TODO `SMTSolvers` cannot return false on satisfiable negations, because formulas other than false have satisfiable
  negations.
* TODO Mathematica name clashes
* TODO Confirm converse contract checking for translations
* TODO Mathematica and SMT: clarify nary operators like `-` and `*`
* TODO Synchronize query index updating (concurrent tool uses)
* TODO Enforce memory management for Mathematica input expressions
* TODO SMT conversion: power handling has inconsistencies
* TODO SMT conversion: `^1` handling needs to be checked since translated as `(* x)`
* TODO Safeguard return values from SMT solvers
* TODO Polya should improve like Z3 does

### Code Review: KeYmaera X Core Delta: 2016-06-01

* NOTE Could turn DifferentialProgram into non-Program.
* TODO Turn `[:=] assign exists` into `DerivedAxiom`
* TODO Add checksum test and core version to string representation of `Lemma`. And `Lemma` name sanity.

###Code Review: KeYmaera X Core: 2016-03-09

`SetLattice` reviewed and changed to pair matching style to improve readability. A few name changes.

* NOTE Fixed `Skolemize` which was found to be unsound because of checking only with respect to literal mentions of free
  variables via `freeVars(e).symbols` instead of `freeVars(e)`.

### Code Review: KeYmaera X Core except `SetLattice`: 2016-03-08

* NOTE `Rule.LAX_MODE=true` has become acceptable but not preferred since not needed in theory.
* TODO Confirm that `ODESystem` should turn into non-`DifferentialProgram` while `DifferentialProgram` should turn into
  non-`Program`.
* TODO Delete `Sequent.pref`
* TODO Turn `[:=] assign exists` into DerivedAxiom
* TODO Add checksum test and core version to string representation of `Lemma`. And `Lemma` name sanity.

### Extended Code Review: KeYmaera X Core: 2015-08-25

* TODO `Rule.LAX_MODE=false`, which affects `BoundVariableRenaming` and `URename` and RCF trusted tools
* TODO `FileLemmaDB.scala`: move out of core
* TODO `Proof.scala`: occasionally determine whether `ClosingRule` etc. categorization is useful
* TODO `SMTConversions.scala`: resolve issues

### Code Review: KeYmaera X Core: 2015-08-24

* TODO `Proof.scala`: `BoundVariableRenaming.compatibilityMode` should be false
* TODO `Proof.scala`: `UniformRenaming.semanticRenaming` should be false
* TODO `FileLemmaDB.scala`: move out of core
* TODO `Proof.scala`: occasionally determine whether `ClosingRule` etc. categorization is useful

### Code Review: KeYmaera X Core: 2015-05-01

* TODO `Proof.scala`: `BoundVariableRenaming.compatibilityMode` should be false
* TODO `AxiomBase.scala`: Code Review confirms that DE needs `?` not to have a `'`.
