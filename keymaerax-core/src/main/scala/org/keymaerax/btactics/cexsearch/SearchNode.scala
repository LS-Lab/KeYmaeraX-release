/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.cexsearch

/** Created by bbohrer on 4/24/16. */
trait SearchNode {
  def goal: Option[ConcreteState]
  def value: Float
  def children: Set[SearchNode]
}
