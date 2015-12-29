package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, Position, SuccPosition}

/** Locates positions */
trait PositionLocator {
  def prettyString: String
}

/** Locates the formula at the specified position. */
case class Fixed(pos: Position, shape: Option[Formula] = None, exact: Boolean = true) extends PositionLocator {
  override def prettyString: String = pos.prettyString
}

/** Locates the first applicable position that matches shape (exactly or unifiably) at or after start of goal. */
case class Find(goal: Int, shape: Option[Formula], start: Position, exact: Boolean = true) extends PositionLocator {
  override def prettyString: String = "'_"
}

/** Locates the last position in the antecedent. */
case class LastAnte(goal: Int) extends PositionLocator {
  override def prettyString: String ="'Llast"
}

/** Locates the last position in the succedent. */
case class LastSucc(goal: Int) extends PositionLocator {
  override def prettyString: String ="'Rlast"
}