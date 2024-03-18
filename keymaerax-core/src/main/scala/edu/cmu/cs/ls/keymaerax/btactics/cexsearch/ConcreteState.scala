/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

import edu.cmu.cs.ls.keymaerax.core.{NamedSymbol, Term}

import scala.collection.immutable.HashMap

/** Created by bbohrer on 4/24/16. */

case class ConcreteState(map: Map[NamedSymbol, Term])
