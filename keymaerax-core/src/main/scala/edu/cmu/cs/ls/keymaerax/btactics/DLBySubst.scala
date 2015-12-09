package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{SequentType, USubstPatternTactic}
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics._
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

/**
  * This is an example of how to implement some of the dL tactics using substitution tactics.
  * Created by nfulton on 11/3/15.
  */
object DLBySubst {
  /**
    * Box monotonicity.
    * {{{
    *      p |- q
    *   -------------monb
    *   [a]p |- [a]q
    * }}}
    */
  def monb = {
    val pattern = SequentType(Sequent(Nil, IndexedSeq("[a_;]p_(??)".asFormula), IndexedSeq("[a_;]q_(??)".asFormula)))
    USubstPatternTactic(
      (pattern, (ru:RenUSubst) => ru.getRenamingTactic & axiomatic("[] monotone", ru.substitution.usubst))::Nil //@todo not sure about how to handle the renaming portion?
    )
  }

  /**
   * Diamond monotonicity.
   * {{{
   *      p |- q
   *   -------------mond
   *   <a>p |- <a>q
   * }}}
   */
  def mond = {
    val pattern = SequentType(Sequent(Nil, IndexedSeq("<a_;>p_(??)".asFormula), IndexedSeq("<a_;>q_(??)".asFormula)))
    USubstPatternTactic(
      (pattern, (ru:RenUSubst) => ru.getRenamingTactic & axiomatic("<> monotone", ru.substitution.usubst))::Nil //@todo not sure about how to handle the renaming portion?
    )
  }

  /** G: Gödel generalization rule reduces a proof of `|- [a;]p(x)` to proving the postcondition `|- p(x)` in isolation.
    * {{{
    *       p(??)
    *   ----------- G
    *    [a;]p(??)
    * }}}
    * @see [[monb]] with p(x)=True
    */
  lazy val G = {
    val pattern = SequentType(Sequent(Nil, IndexedSeq(), IndexedSeq("[a_;]p_(??)".asFormula)))
    USubstPatternTactic(
      (pattern, (ru:RenUSubst) => ru.getRenamingTactic & axiomatic("Goedel", ru.substitution.usubst))::Nil
    )
  }
}
