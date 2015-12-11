package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._

import scala.collection.immutable
import scala.language.postfixOps


/**
 * [[FOQuantifierTactics]] provides tactics for instantiating quantifiers.
 */
object FOQuantifierTactics {
  def allInstantiate(quantified: Option[Variable], instance: Option[Term]): DependentPositionTactic =
    new DependentPositionTactic("all instantiate") {
      override def apply(pos: Position): DependentTactic = new DependentTactic(name) {
        override def computeExpr(v : BelleValue): BelleExpr = v match {
          case BelleProvable(provable) => createTactic(provable, pos)
        }
      }

      def createTactic(provable: Provable, pos: Position): BelleExpr = {
        require(provable.subgoals.size == 1, "Provable must have exactly 1 subgoal, but got " + provable.subgoals.size)
        val sequent = provable.subgoals.head
        def vToInst(vars: Seq[Variable]) = if (quantified.isEmpty) vars.head else quantified.get
        def inst(vars: Seq[Variable]) = if (instance.isEmpty) vToInst(vars) else instance.get
        sequent.at(pos) match {
          case (ctx, f@Forall(vars, qf)) if quantified.isEmpty || vars.contains(quantified.get) =>
            require((if (pos.isAnte) -1 else 1) * FormulaTools.polarityAt(ctx(f), pos.inExpr) < 0, "\\forall must have negative polarity")
            val pattern = SequentType(Sequent(
              Nil,
              immutable.IndexedSeq(),
              immutable.IndexedSeq("(\\forall x p(x)) -> p(t())".asFormula)))
            val allInstantiateAxiom = USubstPatternTactic((pattern, (ru:RenUSubst) =>
              ru.getRenamingTactic & ProofRuleTactics.axiomatic("all instantiate", ru.substitution.usubst))::Nil
            )

            def forall(h: Formula) = if (vars.length > 1) Forall(vars.filter(_ != vToInst(vars)), h) else h
            // cut in p(t) from axiom: \forall x. p(x) -> p(t)
            val p = forall(SubstitutionHelper.replaceFree(qf)(vToInst(vars), inst(vars)))
            val axiomInstance = if (pos.isAnte) Imply(ctx(f), ctx(p)) else ctx(p)
            if (pos.isAnte) {
              ProofRuleTactics.cut(axiomInstance) <(
                (modusPonens(pos, new AntePosition(sequent.ante.length)) & hideL(pos.topLevel)) partial,
                cohide('Rlast) & debug("allLFoo") & CMon(pos.inExpr) & debug("allLBar") & allInstantiateAxiom
                )
            } else {
              ProofRuleTactics.cut(axiomInstance) <(
                cohide2(new AntePosition(sequent.ante.length), pos.topLevel) &
                  TactixLibrary.by(CMon(ctx)(Provable.startProof(Sequent(Nil, immutable.IndexedSeq(f), immutable.IndexedSeq(p))))) &
                  implyRi & allInstantiateAxiom,
                hideR(pos.topLevel) partial
                )
            }
          case (_, (f@Forall(v, _))) if quantified.isDefined && !v.contains(quantified.get) =>
            throw new BelleError("Cannot instantiate: universal quantifier " + f + " does not bind " + quantified.get)
          case (_, f) =>
            throw new BelleError("Cannot instantiate: formula " + f.prettyString + " at pos " + pos + " is not a universal quantifier")
          case _ =>
            throw new BelleError("Position " + pos + " is not defined in " + sequent.prettyString)
        }
      }
  }

  def existsInstantiate(quantified: Option[Variable], instance: Option[Term]): DependentPositionTactic =
    new DependentPositionTactic("exists instantiate") {
      override def apply(pos: Position): DependentTactic = new DependentTactic(name) {
        override def computeExpr(v : BelleValue): BelleExpr =
          useAt("exists dual", PosInExpr(1::Nil))(pos) & 
          allInstantiate(quantified, instance)(pos.first) & useAt("!! double negation")(pos)
      }
    }
}
