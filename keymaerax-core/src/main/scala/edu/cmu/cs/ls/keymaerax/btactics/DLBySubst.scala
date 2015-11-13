package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, NamedTactic, SequentType, USubstPatternTactic}
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics._
import edu.cmu.cs.ls.keymaerax.core.{USubst, Sequent}
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
  val monb = new NamedTactic("monb", {
    val pattern = SequentType(Sequent(Nil, IndexedSeq("[a_;]p_(??)".asFormula), IndexedSeq("[a_;]q_(??)".asFormula)))
    USubstPatternTactic(Seq(
      (pattern, (ru:RenUSubst) => ru.getRenamingTactic & axiomatic("[] monotone", ru.substitution.usubst)) //@todo not sure about how to handle the renaming portion?
    ))
  })

}
