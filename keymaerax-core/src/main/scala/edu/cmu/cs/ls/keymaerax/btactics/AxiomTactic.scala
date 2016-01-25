package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, AntePosition, Position, DependentPositionTactic}
import edu.cmu.cs.ls.keymaerax.btactics
import edu.cmu.cs.ls.keymaerax.core._
import btactics.ProofRuleTactics._
import TacticFactory._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.tools.Tool

/**
  * Created by bbohrer on 1/24/16.
  */
object AxiomTactic {

  /**
    * Creates a new tactic that uses equivalence congruence or equation congruence or monotone to uncover an axiom inside
    * a context.
    * @param axiomName The name of the axiom.
    * @param axiomInstance The axiom instance that should be used in context (an equivalence or equality).
    * @param baseT The base tactic to show the axiom instance once uncovered.
    * @return The new tactic.
    * @todo use CutLeft+CutRight+EquivifyRight for efficiency instead of cut etc.
    */
  def uncoverAxiom(axiomName: String,
                    axiomInstance: Formula => Formula,
                    baseT: Formula => DependentPositionTactic): DependentPositionTactic = axiomName by ((p: Position, sequent:Sequent) => {
        axiomInstance(sequent.at(p)._1.ctx) match {
          case inst@Equiv(f, g) =>
            ContextTactics.cutInContext(inst, p) <(
              /* use*/
              EqualityTactics.equivRewriting(AntePosition(sequent.ante.length))(p.top),
              /* show */
              ProofRuleTactics.coHide('Rlast) & HilbertCalculus.CE(p.inExpr) & baseT(sequent.at(p)._1.ctx)('Rlast)
            )
          case inst@Imply(f, g) if p.isAnte =>
            ContextTactics.cutImplyInContext(inst, p) <(
              /* use */
              implyR('Llast) <(
                TactixLibrary.closeId,
                /*DebuggingTactics.assert(sequent(p), axiomName + ": hiding original instance") & */hide(p.top)) ,
              coHide('Rlast) & implyR('Rlast) & (propositionalCongruence(p.inExpr) | TactixLibrary.nil) &
                DebuggingTactics.assert(1, 1) /*& DebuggingTactics.assert(f, name + ": unexpected formula in ante", 'Llast))*/ /*& DebuggingTactics.assert(g, 'Rlast, axiomName + ": unexpected formula in succ")*/) &
                cut(inst) <(
                  /* use */
                  implyL('Llast) & trivialCloser,
                    /* show */
                  coHide('Rlast) & baseT(sequent.at(p)._1.ctx)('Rlast))
          case inst@Imply(f, g) if !p.isAnte =>
            ContextTactics.cutImplyInContext(inst, p) <(
              /* use */
              implyL('Llast) <(
                /*DebuggingTactics.assert(sequent(p), axiomName + ": hiding original instance") &*/ hide(p.topLevel),
                trivialCloser),
              /* show*/
               coHide('Rlast) & implyR('Rlast) & (propositionalCongruence(p.inExpr) | TactixLibrary.nil) &
                DebuggingTactics.assert(1, 1) & /*DebuggingTactics.assert(f, 'Llast, name + ": unexpected formula in ante") & assert(g, 'Rlast name + ": unexpected formula in succ")) &*/
                cut(inst) <(
                  /* use */
                  implyL('Llast) & trivialCloser,
                 /* show */
                coHide('Rlast) & baseT(sequent.at(p)._1.ctx)('Rlast))
              )
          case Equal(lhs, rhs) => ???
        }})
  
  /**
    * Creates a new tactic to show an axiom by lookup.
    * @param axiomName The name of the axiom.
    * @param subst A function fml => subst to create the substitution from the current axiom form fml (an equivalence or equality).
    * @param alpha A function fml => alpha to create tactic for alpha renaming after substitution from the current axiom form fml.
    * @param axiomInstance A function (fml, axiom) => axiomInstance to generate the axiom instance from the axiom
    *                      form as in the axiom file and the current form fml as in the sequent.
    * @return The new tactic.
    */
  def axiomLookupBase(axiomName: String,
                       subst: Formula => List[SubstitutionPair],
                       alpha: Formula => DependentPositionTactic,
                       axiomInstance: (Formula, Formula) => Formula): DependentPositionTactic = axiomName by ((p:Position, sequent:Sequent) => {
      val axiom = AxiomInfo(axiomName).formula
      val debugMessagePrefix = "[axiomLoopBaseT on " + axiomName + "]"
      val fml = sequent.at(p)._1.ctx
          DebuggingTactics.debug(debugMessagePrefix + " begin") &
            PropositionalTactics.uniformSubst(subst(fml), Map(fml -> axiomInstance(fml, axiom))) &
            DebuggingTactics.debug(s"$debugMessagePrefix substitution succeeded.") &
            DebuggingTactics.assert(0, 1) & /*DebuggingTactics.assert(axiomInstance(fml, axiom), 'Rlast, axiomName + ": unexpected uniform substitution result")) & */
            alpha(fml)('Rlast) & DebuggingTactics.debug(s"$debugMessagePrefix alpha renaming succeeded for axiom $axiomName") &
            /*assert(axiom, 'Rlast, name + ": unexpected axiom form in succedent")) & */ AxiomTactic.axiom(axiomName)}
        )

  /**
    * Axiom lookup imports an axiom into the antecedent.
    */
  def axiom(id: String): BelleExpr = { AxiomInfo(id).belleExpr.asInstanceOf[BelleExpr] }
}
