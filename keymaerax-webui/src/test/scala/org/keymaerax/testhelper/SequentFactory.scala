/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.testhelper

import org.keymaerax.core.{Formula, NamedSymbol, Sequent}

/**
 * Created by smitsch on 1/20/15.
 * @author
 *   Stefan Mitsch
 * @author
 *   Ran Ji
 */
object SequentFactory {

  /**
   * Creates a new sequent with the specified prefixes pref, antecedents ante, and succedents succ.
   * @param pref
   *   The list of prefix symbols.
   * @param ante
   *   The list of antecedent formulas.
   * @param succ
   *   The list of succedent formulas.
   * @return
   *   The new sequent.
   */
  def sequent(pref: Seq[NamedSymbol], ante: Seq[Formula], succ: Seq[Formula]) =
    Sequent(ante.toIndexedSeq, succ.toIndexedSeq)

  /**
   * Create a new sequent with only succedent f, but no specified prefixes or antecedents
   * @param f
   *   The succedent formula.
   * @return
   *   The new sequent.
   */
  def sucSequent(f: Formula) = sequent(Nil, Nil, f :: Nil)
}
