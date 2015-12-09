package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, Position, SuccPosition}

/** Locates positions */
trait PositionLocator {
  def prettyString: String
}

/** Locates the formula at the specified position. */
case class Fixed(pos: Position) extends PositionLocator {
  override def prettyString: String = pos.prettyString
}

/** Locates the first applicable position at or after start of goal. */
case class Find(goal: Int, shape: Option[Formula], start: Position) extends PositionLocator {
  override def prettyString: String = "'_"
}