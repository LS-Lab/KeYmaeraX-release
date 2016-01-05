/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax

/**
  * Proof-term checker turns proof terms to proof certificates.
  * [[edu.cmu.cs.ls.keymaerax.pt.ProofChecker]] turns a [[edu.cmu.cs.ls.keymaerax.pt.ProofTerm proof term]] to the [[edu.cmu.cs.ls.keymaerax.core.Provable]] that it proves.
  * {{{
  *   ProofChecker : ProofTerm * Formula => Provable
  * }}}
  * This package defines
  *   - [[edu.cmu.cs.ls.keymaerax.pt.ProofTerm Proof term]] language
  *   - [[edu.cmu.cs.ls.keymaerax.pt.ProofChecker]] to interpret the proof term language
  * @author Nathan Fulton
  */
package object pt {}
