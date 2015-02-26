package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

/**
 * Implementation of search tactics.
 */
object SearchTacticsImpl {
  def locateSubposition(p : Position, cond: Expr => Boolean = _ => true)(pT : PositionTactic) : Tactic =
      new ApplyPositionTactic("LocateSubposition(" + pT.name + ")", pT) {
    override def findPosition(s: Sequent): Option[Position] = {
      val fn = new ExpressionTraversalFunction {
        var result : Option[Position] = None
        override def preF(p : PosInExpr, f : Formula) = {
          val position = makePos(p)
          if(isSubpos(position) && cond(TacticLibrary.TacticHelper.getFormula(s, position)) &&
            pT.applies(s, position)) { result = Some(position); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
        }
      }
      ExpressionTraversal.traverse(fn, s(p))
      fn.result
    }
    def makePos(pInExpr : PosInExpr) = if(p.isAnte) AntePosition(p.index, pInExpr) else SuccPosition(p.index, pInExpr)
    def isSubpos(pos : Position) = pos.isAnte == p.isAnte && pos.index == p.index && p.inExpr.isPrefixOf(pos.inExpr)

    override def applicable(node: ProofNode): Boolean = findPosition(node.sequent) match {
      case Some(_) => true
      case _ => false
    }
  }

  def locateTerm(posT : PositionTactic, inAnte: Option[Boolean] = None) : Tactic = new ApplyPositionTactic("locateTerm(" + posT.name + ")", posT) {
    override def findPosition(s: Sequent): Option[Position] = inAnte match {
      case Some(ante) if ante =>
        for ((anteF, idx) <- s.ante.zipWithIndex) {
          def appliesInExpr(p: PosInExpr) = posT.applies(s, AntePosition(idx, p))
          findPosInExpr(appliesInExpr, anteF) match {
            case Some(posInExpr) => return Some(AntePosition(idx, posInExpr))
            case None => //
          }
        }
        None
      case Some(ante) if !ante =>
        for ((succF, idx) <- s.succ.zipWithIndex) {
          def appliesInExpr(p: PosInExpr) = posT.applies(s, SuccPosition(idx, p))
          findPosInExpr(appliesInExpr, succF) match {
            case Some(posInExpr) => return Some(SuccPosition(idx, posInExpr))
            case None => //
          }
        }
        None
      case None =>
        for ((anteF, idx) <- s.ante.zipWithIndex) {
          def appliesInExpr(p: PosInExpr) = posT.applies(s, AntePosition(idx, p))
          findPosInExpr(appliesInExpr, anteF) match {
            case Some(posInExpr) => return Some(AntePosition(idx, posInExpr))
            case None => //
          }
        }
        for ((succF, idx) <- s.succ.zipWithIndex) {
          def appliesInExpr(p: PosInExpr) = posT.applies(s, SuccPosition(idx, p))
          findPosInExpr(appliesInExpr, succF) match {
            case Some(posInExpr) => return Some(SuccPosition(idx, posInExpr))
            case None => //
          }
        }
        None
    }

    def findPosInExpr(appliesInExpr : PosInExpr => Boolean, f : Formula) : Option[PosInExpr] = {
      var result : Option[PosInExpr] = None
      val fn = new ExpressionTraversalFunction {
        override def preT(pos : PosInExpr, term : Term) = {
          if(appliesInExpr(pos)) {
            result = Some(pos);
            Left(Some(ExpressionTraversal.stop))
          }
          else {
            Left(None)
          }
        }
      }
      ExpressionTraversal.traverse(fn, f);
      result
    }

    override def applicable(node: ProofNode): Boolean = findPosition(node.sequent) match {
      case Some(_) => true
      case _ => false
    }
  }

  /**
   * Locates a position in the antecedent where the specified position tactic is applicable.
   * @param posT The position tactic.
   * @return A new tactic that applies said tactic at the specified position.
   */
  def locateAnte(posT: PositionTactic): Tactic = new ApplyPositionTactic("locateAnte (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = findPosition(p.sequent).isDefined

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.ante.length) {
        val pos = AntePosition(i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      None
    }
  }

  /**
   * Locates a position in the succedent where the specified position tactic is applicable.
   * @param posT The position tactic.
   * @return A new tactic that applies said tactic at the specified position.
   */
  def locateSucc(posT: PositionTactic): Tactic = new ApplyPositionTactic("locateSucc (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = findPosition(p.sequent).isDefined

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.succ.length) {
        val pos = SuccPosition(i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      None
    }
  }

  /**
   * Applies a position tactic at the last position in the succedent.
   * @param pt The position tactic.
   * @return The new tactic to apply said position tactic at the last position.
   */
  def lastSucc(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " succ.length - 1") {
    override def applicable(node: ProofNode): Boolean =
      pt.applies(node.sequent, SuccPosition(node.sequent.succ.length - 1))

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      Some(pt(SuccPosition(node.sequent.succ.length - 1)))
  }

  /**
   * Applies a position tactic at the last position in the antecedent.
   * @param pt The position tactic.
   * @return The new tactic to apply said position tactic at the last position.
   */
  def lastAnte(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " ante.length - 1") {
    override def applicable(node: ProofNode): Boolean =
      pt.applies(node.sequent, AntePosition(node.sequent.ante.length - 1))

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      Some(pt(SuccPosition(node.sequent.ante.length - 1)))
  }

  /**
   * Creates a new tactic, which applies a tactic on the branch identified with the specified branch label, if such
   * branch exists.
   * @param s The branch label.
   * @param t The tactic to apply on said branch.
   * @return The new tactic.
   */
  def onBranch(s: String, t: Tactic): Tactic = ifT(_.tacticInfo.infos.get("branchLabel") == Some(s), t)

  /**
   * used to say "do equiv-r". On the left branch of that, do my
   * branch1 tactic and on the right brance I want to follow branch2 as a tactic.
   *
   * onBranch is used when you have a very specific tactic you only want to run
   * on a branch where you know it will work. e.g. "I know that tacticX will work
   * on the left side because it's exactly what we need, but tacticX is not useful
   * anywhere else."
   *
   * This could be useful for macro recording so that we can provide a concise
   * proof script of what we did. That way this can be used on another proof where
   * the exact proof steps might not be necessary but the tactic might be very
   * useful.
   *
   * Idea: tie together the interface that we had in KeYmaera with tactic writing
   * (I have an idea what my proof will look like
   */
  def onBranch(s1: (String, Tactic), spec: (String, Tactic)*): Tactic =
    if(spec.isEmpty)
      ifT(_.tacticInfo.infos.get("branchLabel") == Some(s1._1), s1._2)
    else
      switchT((pn: ProofNode) => {
        pn.tacticInfo.infos.get("branchLabel") match {
          case None => NilT
          case Some(l) =>
            val candidates = (s1 +: spec).filter((s: (String, Tactic)) => l == s._1)
            if(candidates.isEmpty) NilT
            else {
              require(candidates.length == 1, "There should be a unique branch with label " + l
                + " however there are " + candidates.length + " containing " + candidates.map(_._1))
              candidates.head._2
            }
        }
      })
}
