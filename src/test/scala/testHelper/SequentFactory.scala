package testHelper

import edu.cmu.cs.ls.keymaera.core.{RootNode, Sequent, Formula, NamedSymbol}

/**
 * Created by smitsch on 1/20/15.
 * @author Stefan Mitsch
 */
object SequentFactory {
  /**
   * Creates a new sequent with the specified prefixes pref, antecedents ante, and succedents succ.
   * @param pref The list of prefix symbols.
   * @param ante The list of antecedent formulas.
   * @param succ The list of succedent formulas.
   * @return The new sequent.
   */
  def sequent(pref: Seq[NamedSymbol], ante: Seq[Formula], succ: Seq[Formula]) =
    new Sequent(pref.to[scala.collection.immutable.Seq],
      ante.to[scala.collection.immutable.IndexedSeq],
      succ.to[scala.collection.immutable.IndexedSeq]
    )

  def sucSequent(f: Formula) = sequent(Nil, Nil, f::Nil)
}
