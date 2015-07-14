/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * KeYmaera Exception and Error Hierarchy
 * @author aplatzer
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.ProverException

class TacticException(msg: String, node: ProofNode) extends ProverException(msg + "\nat " + node.sequent) {}
