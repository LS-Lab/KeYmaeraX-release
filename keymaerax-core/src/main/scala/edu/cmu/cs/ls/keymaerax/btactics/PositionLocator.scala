package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, Position, SuccPosition}

/** Locates positions */
trait PositionLocator {
  def prettyString: String
}

/** Locates the formula at the specified position. */
case class Fixed(pos: Position) extends PositionLocator {
  override def prettyString: String = pos.prettyString
}

/** Locates the first applicable position at or after start in the antecedent of goal. */
case class FindAnte(goal: Int = 0, start: AntePosition = new AntePosition(0)) extends PositionLocator {
  override def prettyString: String = "?a"
}

/** Locates the first applicable position at or after start in the succedent of goal. */
case class FindSucc(goal: Int = 0, start: SuccPosition = new SuccPosition(0)) extends PositionLocator {
  override def prettyString: String = "?s"
}