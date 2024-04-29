# Extending KeYmaera X

**Warning:** The information in this file may be outdated.

## Adding Special Functions

Augmenting KeYmaera X with additional functions with special meaning
is currently best done via adding appropriate function definitions with corresponding lemmas.

Example: addition of `abs`/`min`/`max` functions in `edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms.scala`

## Adding Operators

Adding new built-in operators works as follows:

Prover Core (soundness-critical):

1. Add algebraic datatype to `edu.cmu.cs.ls.keymaerax.core.Expression` data structures.
2. Define free/bound/mustbound variables in `edu.cmu.cs.ls.keymaerax.core.StaticSemantics.apply` or its callees
3. Define signature in `edu.cmu.cs.ls.keymaerax.core.StaticSemantics.signature`
4. Define uniform substitution in `edu.cmu.cs.ls.keymaerax.core.USubstOne.usubst` or its callees
5. Define uniform renaming in `edu.cmu.cs.ls.keymaerax.core.UniformRenaming.URename.apply` or its callees
6. Specify axioms or proof rules in `edu.cmu.cs.ls.keymaerax.core.AxiomBase`

Parser & Pretty-Printer:

1. Augment `edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXLexer.findNextToken` with new tokens for operator (if needed)
2. Define operator notation and precedence in `edu.cmu.cs.ls.keymaerax.parser.OpSpec.op`
3. Augment `edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser.op` with corresponding reverse operator notation lookup.
4. Augment `edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser` first and follow set lookaheads according to grammar.

Example: the addition of the `Dual` operator for hybrid games.
