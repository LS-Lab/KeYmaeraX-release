# Extending KeYmaera X


## Adding Special Functions

Augmenting KeYmaera X with additional functions with special meaning
is currently best done via adding appropriate function definitions with corresponding lemmas.

Example: addition of `abs`/`min`/`max` functions in `org.keymaerax.btactics.DerivedAxioms.scala`

## Adding Operators

Adding new built-in operators works as follows:

Prover Core (soundness-critical):

1. Add algebraic datatype to `org.keymaerax.core.Expression` data structures.
2. Define free/bound/mustbound variables in `org.keymaerax.core.StaticSemantics.apply` or its callees
3. Define signature in `org.keymaerax.core.StaticSemantics.signature`
4. Define uniform substitution in `org.keymaerax.core.USubstOne.usubst` or its callees
5. Define uniform renaming in `org.keymaerax.core.UniformRenaming.URename.apply` or its callees
6. Specify axioms or proof rules in `org.keymaerax.core.AxiomBase`

Parser & Pretty-Printer:

1. Augment `org.keymaerax.parser.DLParser` with the new operators
2. Define operator notation and precedence in `org.keymaerax.parser.OpSpec.op`
3. Augment `org.keymaerax.parser.KeYmaeraXParser.op` with corresponding reverse operator notation lookup
4. Define pretty pretting in `org.keymaerax.parser.KeYmaeraXPrinter.pp`, `org.keymaerax.parser.KeYmaeraXFullPrinter.pp`
and `org.keymaerax.parser.KeYmaearXPrettierPrinter.docOf` or their callees

General Infrastructure & Implementing Tactics:

1. Define unification in `org.keymaerax.infrastruct.SchematicUnificationMatch.unify` and
`org.keymaerax.infrastruct.UniformMatching.unify` or their callees
2. Define uniform substitution and uniform renaming combined in `org.keymaerax.infrastruct.USubstRenOne.usubst` or its 
callees
3. Define context operations in `org.keymaerax.infrastruct.Context.{context, part, replaceAt}` or their callees
4. Define annotated axioms in `org.keymaerax.btactics.Ax` and annotated tactics in `org.keymaerax.btactics`

Example: the addition of the `Refinement` operator for dRL.
