/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

/**
 * Proof-term checker turns proof terms to proof certificates. [[org.keymaerax.pt.ProofChecker]] turns a
 * [[org.keymaerax.pt.ProofTerm proof term]] to the [[org.keymaerax.core.Provable]] that it proves.
 * {{{
 *   ProofChecker : ProofTerm * Formula => Provable
 * }}}
 * This package defines
 *   - [[org.keymaerax.pt.ProofTerm Proof term]] language
 *   - [[org.keymaerax.pt.ProofChecker]] to interpret the proof term language
 * @author
 *   Nathan Fulton
 */
package object pt {}
