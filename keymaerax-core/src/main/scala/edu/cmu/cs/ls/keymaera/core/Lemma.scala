package edu.cmu.cs.ls.keymaera.core

import edu.cmu.cs.ls.keymaera.parser.Evidence

/**
 * Created by smitsch on 4/28/15.
 * @author Stefan Mitsch
 */
final case class Lemma(fact: Provable, evidence: List[Evidence], name: Option[String] = None)
