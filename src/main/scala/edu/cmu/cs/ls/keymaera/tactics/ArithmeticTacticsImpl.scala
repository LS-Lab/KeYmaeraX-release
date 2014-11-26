package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import TacticLibrary.{universalClosure,instantiateT,closeT,hideT,onBranch,CloseTrueT}
import BuiltinHigherTactics.stepAt
import PropositionalTacticsImpl.{AndLeftT,NotLeftT,EquivLeftT}
import SearchTacticsImpl.{locateAnte,locateSucc}

import scala.collection.immutable.{Set, Seq}

/**
 * Implementation of arithmetic tactics.
 */
object ArithmeticTacticsImpl {

  /**
   * The quantifier elimination tactic.
   * @param toolId The quantifier elimination tool to use.
   * @return The tactic.
   */
  protected[tactics] def quantifierEliminationT(toolId: String): Tactic = new Tactic("Quantifier Elimination") {
    def qeApplicable(s: Sequent): Boolean =
      (s.ante ++ s.succ).foldLeft(true)((acc: Boolean, f: Formula) => acc && qeApplicable(f))
    def qeApplicable(f: Formula): Boolean = {
      var qeAble = true
      val fn = new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          e match {
            case Modality(_, _) => qeAble = false
            case ApplyPredicate(_, _) => qeAble = false
            case PredicateConstant(_, _) => qeAble = false
            case _ =>
          }
          if (qeAble) Left(None) else Left(Some(new StopTraversal {}))
        }

        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          e match {
            case Pair(_, _, _) => qeAble = false
            case Apply(fun, _) => qeAble = false // check if fun is an external function
            case Derivative(_, _) => qeAble = false
            case IfThenElseTerm(_, _, _) => qeAble = false
            case _ =>
          }
          if (qeAble) Left(None) else Left(Some(new StopTraversal {}))
        }
      }
      ExpressionTraversal.traverse(fn, f)
      qeAble
    }
    override def applicable(node: ProofNode): Boolean = qeApplicable(node.sequent)

    override def apply(tool: Tool, node: ProofNode): Unit = {
      val t: Tactic = new ConstructionTactic("Mathematica QE") {
        override def applicable(node: ProofNode): Boolean = true

        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
          LookupLemma.addRealArithLemma(tool, universalClosure(desequentialization(node.sequent))) match {
            case Some((file, id, f)) =>
              f match {
                case Equiv(res, True) => {
                  val lemma = new ApplyRule(LookupLemma(file, id)) {
                    override def applicable(node: ProofNode): Boolean = true
                  }
                  // reinstantiate quantifiers
                  val pos = AntePosition(node.sequent.ante.length)
                  def reInst(f: Formula): Option[Tactic] = f match {
                    case Forall(v, g) => {
                      val resG = reInst(g)
                      if (v.isEmpty) resG
                      else {
                        val vars = v.map(n => n match {
                          case x: Variable => x
                          case _ => throw new IllegalArgumentException("Can only handle quantifiers over variables")
                        })
                        val tac = (for (n <- vars) yield instantiateT(n, n)(pos)).reduce(seqT)
                        resG match {
                          case Some(t) => Some(tac & t)
                          case None => Some(tac)
                        }
                      }
                    }
                    case _ => None
                  }
                  val contTactic = ((closeT | locateSucc(stepAt(true, false, true)) | locateAnte(stepAt(true, false, true, true)))*)
                  def branch1(inst: Tactic): Tactic = AndLeftT(pos) & hideT(pos + 1) & inst & contTactic
                  //Really simple because this is just checking that the thing we believe to be true is actually true.
                  val branch2 = AndLeftT(pos) & NotLeftT(AntePosition(node.sequent.ante.length + 1)) & CloseTrueT(SuccPosition(node.sequent.succ.length))
                  val tr = reInst(res) match {
                    case Some(inst) => lemma & EquivLeftT(pos) & onBranch((equivLeftLbl, branch1(inst)), (equivRightLbl, branch2))
                    case _ => lemma & contTactic
                  }
                  Some(tr )//& debugT("Test"))
                }
                case _ => println("Only apply QE if the result is true, have " + f.prettyString()); None
              }
            case _ => None
          }
        }
      }
      t.scheduler = Tactics.MathematicaScheduler
      t.continuation = continuation
      t.dispatch(this, node)
    }
  }

  /**
   * Tactic to hide unnecessary equations in the antecedent.
   * @return The tactic.
   */
  protected[tactics] def hideUnnecessaryLeftEqT: Tactic = new ConstructionTactic("Hide Equations") {
    import Helper.names
    def collectEquations(s: Sequent): Seq[(Int, Term, Term)] =
      (for(i <- 0 until s.ante.length)
      yield s.ante(i) match {
          case Equals(_, a, b) if names(a).intersect(names(b)).isEmpty => Some((i, a, b))
          case _ => None
        }
        ).flatten

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val eqS: Seq[(Int, Term, Term)] = collectEquations(node.sequent)
      val s = node.sequent
      val anteNames = for (i <- 0 until s.ante.length)
      yield (i, Helper.certainlyFreeNames(s.ante(i)))

      val succNames = s.succ.map(Helper.certainlyFreeNames(_)).flatten

      val res = (for ((i, l, r) <- eqS)
      yield if (succNames.contains(l)
          || anteNames.filter((j: (Int, Set[NamedSymbol])) => i != j._1).map(_._2).flatten.contains(l)) None
        else Some(i)
        ).flatten.sortWith((i: Int, j: Int) => i > j)
      if(res.isEmpty) Some(NilT) else Some(res.map((i: Int) => hideT(AntePosition(i))).reduce(seqT(_, _)))
    }

    override def applicable(node: ProofNode): Boolean = true
  }

  /**
   * Turns a sequent into a form suitable for quantifier elimination.
   * @param s The sequent.
   * @return The desequentialized form.
   */
  private def desequentialization(s : Sequent) = {
    //TODO-nrf Not sure what to do with pref. Matters in non-taut case.
    if(s.ante.isEmpty && s.succ.isEmpty) False
    else {
      val assumption =
        if(s.ante.isEmpty) True
        else s.ante.reduce( (l,r) => And(l,r) )

      val implicant =
        if(s.succ.isEmpty) Not(assumption)
        else s.succ.reduce( (l,r) => Or(l,r) )

      if(s.ante.isEmpty) implicant
      else Imply(assumption, implicant)
    }
  }
}
