/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.SyntacticDerivationInContext.ApplicableAtFormula
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tools.Tool

/**
 * Implementation of search tactics.
 */
object SearchTacticsImpl {
  def locateSubposition(p : Position, cond: Expression => Boolean = _ => true)(pT : PositionTactic) : Tactic =
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

  def locateLargestSubformula(t : (PositionTactic with ApplicableAtFormula)) : PositionTactic = {
    val predicate = (f : Formula) => t.applies(f)
    locateLargestSubformula(predicate, t)
  }

  /**
    *
    * @param pred A predicate over formulas defining where the tactic should be applied.
   *             I.e., it should be that pred(f) implies t.applies(s,p) whenever s(p) = f.
    * @param t
    * @return Tactic that applies t to largest position for which pred holds in p.
    */
  def locateLargestSubformula(pred : Formula => Boolean, t : PositionTactic) =
  new PositionTactic("locate largest subformula") {
    override def applies(s: Sequent, p: Position): Boolean = largestPredPos(TacticHelper.getFormula(s,p)).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val f = TacticHelper.getFormula(node.sequent,p)
        largestPredPos(f) match {
          case Some(pApp) => Some(t(p.subPos(pApp)))
          case None => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    def largestPredPos(formula : Formula) : Option[PosInExpr] = {
      var pos : Option[PosInExpr] = None
      val traversal = new ExpressionTraversalFunction {
        override def preF(p : PosInExpr, f : Formula) = {
          if(pred(f)) {
            pos = Some(p);
            Left(Some(ExpressionTraversal.stop))
          }
          else Left(None)
        }
      }
      ExpressionTraversal.traverse(traversal, formula);
      pos
    }
  }

  /**
   * Finds the position of a in f(a) <-> f(b), and applies congT at that position.
   * @param a The left term.
   * @param b The right term
   * @param congT The congruence tactic.
   * @return Result of running congT on the position of a, given a position containing f(a) <-> f(b).
   */
  def locateForCongruenceRewriting(a : Term, b : Term, congT : PositionTactic) =
  new PositionTactic("locate for congurnece rewriting") {
    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && (s(p) match {
      case Equiv(_,_) => true
      case _          => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic("Construct " + name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Equiv(fa, fb) => findPosInExpr(fa, fb) match {
          case Some(posInExpr) => {
            // posInExpr is the position of a in fa, so to get the position of a in fa <-> fb we have to prepend a 0.
            val position =
              if(p.isAnte) AntePosition(p.index, PosInExpr(0 +: posInExpr.pos))
              else SuccPosition(p.index, PosInExpr(0 +: posInExpr.pos))
            Some(congT(position))
          }
          case None => None
        }
        case _ => None
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    /**
     * Finds the position of the first occurence of a in fa.
     * @param fa LHS of Equiv
     * @param fb RHS of Equiv
     * @return Some position of the first occurrence of the term a **in fa** iff b occurs at the same position in fb.
     *         If a cannot be found in fa or if the corresponding position in fb is not equal to b, then None.
     */
    private def findPosInExpr(fa : Formula, fb : Formula) : Option[PosInExpr] = {
      var retVal : Option[PosInExpr] = None

      val traversalFn = new ExpressionTraversalFunction {
        def preExpression(p : PosInExpr, e : Expression) = {
          if (e == a) {
            TacticHelper.getTerm(fb, p) match {
              case Some(bCandidate) => {
                if(bCandidate == b) {
                  retVal = Some(p)
                  Left(Some(ExpressionTraversal.stop))
                }
                else {
//                  println("Skipping this candidate because b != " + TacticHelper.getTerm(fb, p))
                  Left(None)
                }
              }
              case None => Left(None)
            }
          }
          else Left(None)
        }

        override def preT(p : PosInExpr, t : Term) = preExpression(p,t)
        override def preF(p : PosInExpr, f : Formula) = preExpression(p,f)
        override def preP(p : PosInExpr, program : Program) = preExpression(p,program)
      }

      ExpressionTraversal.traverse(traversalFn, fa)
      retVal
    }
  }

  /**
   * Locates the first expression and position in the sequent for which pred is true.
   * @author Nathan Fulton
   * @param posT The tactic to apply at the found position.
   * @param pred A predicate defined in terms of expressions and positions in expressions.
   * @param inAnte Determines if we should search the ante or succ.
   * @return A tactic that applies posT and is applicable iff there is a position where pred holds and posT is applicable.
   */
  def locateByPredicate(posT : PositionTactic, pred : (PosInExpr, Expression, Sequent) => Boolean, inAnte : Boolean = false) : Tactic =
    new ApplyPositionTactic("locateByPredicate(" + posT.name + ")", posT) {

      override def findPosition(s: Sequent): Option[Position] = {
        def firstApplicablePosition(fs : IndexedSeq[Formula], isAnte : Boolean) : Option[Position] = {
          (fs zip List.range(0, fs.length))
            .map(indexedElement => {
            val f     = indexedElement._1
            val index = indexedElement._2

            var applicablePosAndExpr : Option[(PosInExpr, Expression)] = None
            ExpressionTraversal.traverse(new ExpressionTraversalFunction {
              override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
                if (pred(p, e, s)) {
                  applicablePosAndExpr = Some(p, e)
                  Left(Some(ExpressionTraversal.stop))
                }
                else Left(None)
              }
              override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] =
                if(pred(p, e, s)) {
                  applicablePosAndExpr = Some(p, e)
                  Left(Some(ExpressionTraversal.stop))
                }
                else Left(None)
              override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
                if(pred(p, e, s)) {
                  applicablePosAndExpr = Some(p, e)
                  Left(Some(ExpressionTraversal.stop))
                }
                else Left(None)
            }, f)

            (index, applicablePosAndExpr)
          })
            .filter(_._2.isDefined)
            .lastOption match {
            case Some(idxAndPosAndExpr) => {
              val idx : Int = idxAndPosAndExpr._1
              val posAndExpr : Option[(PosInExpr, Expression)] = idxAndPosAndExpr._2
              if(isAnte) Some(AntePosition(idx, posAndExpr.get._1)) //The .get is justified by the filter.
              else       Some(SuccPosition(idx, posAndExpr.get._1))
            }
            case None => None
          }
        }


        if(inAnte) firstApplicablePosition(s.ante, true)
        else       firstApplicablePosition(s.succ, false)
      }

      override def applicable(node: ProofNode): Boolean =
//        findPosition(node.sequent).isDefined
        if(findPosition(node.sequent).isDefined) {println("is applic"); true} else {println("Not applicable"); false}
    }

  def locateTerm(posT : PositionTactic, inAnte: Boolean = false) : Tactic = new ApplyPositionTactic("locateTerm(" + posT.name + ")", posT) {
    override def findPosition(s: Sequent): Option[Position] = if (inAnte) {
      for ((anteF, idx) <- s.ante.zipWithIndex) {
        def appliesInExpr(p: PosInExpr) = posT.applies(s, AntePosition(idx, p))
        findPosInExpr(appliesInExpr, anteF) match {
          case Some(posInExpr) => return Some(AntePosition(idx, posInExpr))
          case None => println(s"No applicable position found for ${posT.name} in $anteF at $idx in ante")//
        }
      }
      None
    } else {
      for ((succF, idx) <- s.succ.zipWithIndex) {
        def appliesInExpr(p: PosInExpr) = posT.applies(s, SuccPosition(idx, p))
        findPosInExpr(appliesInExpr, succF) match {
          case Some(posInExpr) => return Some(SuccPosition(idx, posInExpr))
          case None => println(s"No applicable position found for ${posT.name} in $succF at $idx in succ")//
        }
      }
      None
    }

    def findPosInExpr(appliesInExpr : PosInExpr => Boolean, f : Formula) : Option[PosInExpr] = {
      var result : Option[PosInExpr] = None
      val fn = new ExpressionTraversalFunction {
        override def preT(pos : PosInExpr, term : Term) = {
          if (appliesInExpr(pos)) {
            result = Some(pos)
            Left(Some(ExpressionTraversal.stop))
          } else {
            Left(None)
          }
        }
      }
      ExpressionTraversal.traverse(fn, f)
      result
    }

    override def applicable(node: ProofNode): Boolean = findPosition(node.sequent) match {
      case Some(_) => true
      case _ => false
    }
  }

  /**
   * Locates a position in the antecedent where the specified position tactic is applicable, the specified condition
   * on the formula in that position holds, and the key inside the formula in that position is true.
   * @param posT The position tactic.
   * @param cond The condition, default is true
   * @param key The key, default is None (meaning look for top-level formula).
   * @return A new tactic that applies said tactic at the specified position.
   */
  def locateAnte(posT: PositionTactic, cond: Formula => Boolean = _ => true, key: Option[Expression => Boolean] = None): Tactic =
      new ApplyPositionTactic("locateAnte (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = {
      val pos = findPosition(p.sequent)
      pos.isDefined && cond(p.sequent(pos.get)) && (key match {
        case Some(keyCond) if p.sequent(pos.get).isFormulaAt(pos.get.inExpr) => keyCond(p.sequent(pos.get).subFormulaAt(pos.get.inExpr).get)
        case Some(keyCond) if p.sequent(pos.get).isTermAt(pos.get.inExpr) => keyCond(p.sequent(pos.get).termAt(pos.get.inExpr))
        case None => true
      })
    }

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- s.ante.indices) {
        val topPos = AntePosition(i)
        if (cond(s(topPos))) key match {
          case Some(keyCond) => findKey(posT, s, i, keyCond, (idx, p) => AntePosition(idx, p)) match {
            case Some(p) => return Some(p)
            case None => // continue searching
          }
          case None => if (posT.applies(s, topPos)) return Some(topPos)
        }
      }
      None
    }
  }

  /**
   * Locates a position in the succedent where the specified position tactic is applicable, the specified condition
   * on the formula in that position holds, and the key inside the position is true.
   * @param posT The position tactic.
   * @param cond The condition, default is true.
   * @param key The key, default is None (meaning look for top-level formula).
   * @return A new tactic that applies said tactic at the specified position.
   */
  def locateSucc(posT: PositionTactic, cond: Formula => Boolean = (_ => true), key: Option[Expression => Boolean] = None): Tactic =
      new ApplyPositionTactic("locateSucc (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = {
      val pos = findPosition(p.sequent)
      pos.isDefined && cond(p.sequent(pos.get)) && (key match {
        //@todo the following two cases can be merged by using  p.sequent(pos.get.top).at(pos.get.inExpr), which in turn should be part of a SequentConverter(pos.get) implicit def
        case Some(keyCond) if p.sequent(pos.get).isFormulaAt(pos.get.inExpr) => keyCond(p.sequent(pos.get).subFormulaAt(pos.get.inExpr).get)
        case Some(keyCond) if p.sequent(pos.get).isTermAt(pos.get.inExpr) => keyCond(p.sequent(pos.get).termAt(pos.get.inExpr))
        case None => true
      })
    }

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- s.succ.indices) {
        val topPos = SuccPosition(i)
        if (cond(s(topPos))) key match {
          case Some(keyCond) => findKey(posT, s, i, keyCond, (idx, p) => SuccPosition(idx, p)) match {
            case Some(p) => return Some(p)
            case None => // continue searching
          }
          case None => if (posT.applies(s, topPos)) return Some(topPos)
        }
      }
      None
    }
  }

  /** Finds a position inside the formula s(i) where the specified position tactic is applicable and the specified condition holds */
  private def findKey(posT: PositionTactic, s: Sequent, i: Int, keyCond: Expression => Boolean,
                      posFactory: (Int, PosInExpr) => Position): Option[Position] = {
    var posInExpr: Option[PosInExpr] = None
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        if (keyCond(e) && posT.applies(s, posFactory(i, p))) {
          posInExpr = Some(p)
          Left(Some(ExpressionTraversal.stop))
        } else Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        if (keyCond(e) && posT.applies(s, posFactory(i, p))) {
          posInExpr = Some(p)
          Left(Some(ExpressionTraversal.stop))
        } else Left(None)
      }
    }, s(posFactory(i, HereP)))
    posInExpr match {
      case Some(p) => Some(posFactory(i, p))
      case None => None
    }
  }

  def last(pt: PositionTactic): Tactic = lastSuccAnte(pt)
  def lastSuccAnte(pt: PositionTactic): Tactic = lastSucc(pt) | lastAnte(pt)
  def lastAnteSucc(pt: PositionTactic): Tactic = lastAnte(pt) | lastSucc(pt)

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
      Some(pt(AntePosition(node.sequent.ante.length - 1)))
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
