/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import org.scalatest._

/**
  * Formalized safety proofs for the ACAS X collision avoidance system.
  *
  * @see Jean-Baptiste Jeannin et al.: A Formally Verified Hybrid System for Safe Advisories in the Next-Generation
  *      Airborne Collision Avoidance System, STTT.

  * @see [[AcasXSafe]] for proofs of Sect. 3: Safe Regions for Immediate Pilot Response
  * @see [[AcasXSafeTwoSided]] for proofs of Sect. 5.1: Two-Sided Safe Region with Immediate Pilot Response
  * @see [[AcasXSafeBoundedTime]] for proofs of Sect. 5.2: Bounded-Time Safe Regions
  * @see [[AcasXSafeable]] for proofs of Sect. 5.3: Safeable Region
  *
  * @author Khalil Ghorbal
  * @author Jean-Baptiste Jeannin
  * @author Yanni A. Kouskoulas
  * @author Stefan Mitsch
  * @author Andre Platzer
  */
@SlowTest
class AcasX extends Suites(
  new AcasXSafe,
  new AcasXSafeTwoSided,
  new AcasXSafeBoundedTime,
  new AcasXSafeable
)
