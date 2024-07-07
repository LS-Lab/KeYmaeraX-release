/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.cexsearch

import org.keymaerax.core.{NamedSymbol, Term}

import scala.collection.immutable.HashMap

/** Created by bbohrer on 4/24/16. */

case class ConcreteState(map: Map[NamedSymbol, Term])
