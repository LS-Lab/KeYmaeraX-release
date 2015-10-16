/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * KeYmaera Exception and Error Hierarchy
 * @author Andre Platzer
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.ProverException

class TacticException(msg: String, node: ProofNode) extends ProverException(msg + "\nat " + node.sequent.prettyString) {}
