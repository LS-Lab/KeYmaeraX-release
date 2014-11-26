package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper.getFormula
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ApplyRule, ConstructionTactic, Tactic, PositionTactic}

import TacticLibrary.{alphaRenamingT,uniformSubstT,axiomT}

import scala.collection.immutable.List
import scala.collection.immutable.Seq

/**
 * Implementation of first order quantifier tactics.
 */
object FOQuantifierTacticsImpl {

  /**
   * Creates a tactic which does quantifier instantiation.
   * @param quantified The quantified variable.
   * @param instance The instance.
   * @return The tactic.
   */
  def instantiateT(quantified: Variable, instance: Term): PositionTactic = new PositionTactic("Quantifier Instantiation") {
    val axiomName = "Quantifier Instantiation"
    val axiom = Axiom.axioms.get(axiomName)
    require(axiom.isDefined)

    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case Forall(_, _) => true
      case _ => false
    })

    override def apply(pos: Position): Tactic = new ConstructionTactic("Quantifier Instantiation") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      def replace(f: Formula)(o: Variable, n: Term): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Forall(v, fa) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), fa))
          case Exists(v, fa) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), fa))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
      }, f) match {
        case Some(g) => g
        case None => throw new IllegalStateException("Replacing one variable by another should not fail")
      }

      def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution, (Variable, Variable), (Term, Variable))] = f match {
        case Forall(x, qf) if x.contains(quantified) =>
          def forall(h: Formula) = if (x.length > 1) Forall(x.filter(_ != quantified), h) else h
          // construct substitution
          val aX = Variable("x", None, Real)
          val aXDD = Variable("$$x", None, Real)
          val aT = Variable("t", None, Real)
          val aP = Function("p", None, Real, Bool)
          val l = List(new SubstitutionPair(ApplyPredicate(aP, aXDD), forall(replace(qf)(quantified, aXDD))))
          // construct axiom instance: \forall x. p(x) -> p(t)
          val g = replace(qf)(quantified, instance)
          val axiomInstance = Imply(f, forall(g))
          Some(axiomInstance, Substitution(l), (quantified, aX), (instance, aT))
        case Forall(x, qf) if !x.contains(quantified) =>
          println(x + " does not contain " + quantified)
          x.map({
            case x: NamedSymbol => println("Symbol " + x.name + " " + x.index)
            case _ =>
          })
          None
        case _ =>
          println("Cannot instantiate quantifier for " + quantified.prettyString() + " in " + f.prettyString())
          None
      }

      def decompose(d: Formula): Formula = d match {
        case Forall(v, f) if v.length > 1 => Forall(v.take(1), Forall(v.drop(1), f))
        case Exists(v, f) if v.length > 1 => Exists(v.take(1), Exists(v.drop(1), f))
        case _ => d
      }

      // since we have an implication, we use modus ponens to get it's consequence
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        axiom match {
          case Some(a) =>
            constructInstanceAndSubst(getFormula(node.sequent, pos)) match {
              case Some((axiomInstance, subst, (quant, aX), (inst, aT))) =>
                val eqPos = AntePosition(node.sequent.ante.length)
                val branch1Tactic = modusPonensT(pos, eqPos)
                // val hideAllAnte = for (i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                // val hideAllSuccButLast = for (i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                // val hideSllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
                def alpha(p: Position, q: Variable) = alphaRenamingT(q.name, q.index, "$" + aX.name, aX.index)(p)
                def repl(f: Formula, v: Variable, atTrans: Boolean = true):Formula = f match {
                  case Imply (aa, b) => Imply(decompose(replace (aa)(v, Variable ("$" + aX.name, aX.index, aX.sort) )), if(atTrans) replace(b)(aT, inst) else b)
                  case _ => throw new IllegalArgumentException("...")
                }
                val replMap = Map(repl(axiomInstance, quant, atTrans = false) -> repl(a, aX))
                val branch2Tactic = cohideT(SuccPosition(node.sequent.succ.length)) ~
                  alpha(SuccPosition(0, HereP.first), quant) ~
                  decomposeQuanT(SuccPosition(0, HereP.first)) ~
                  (uniformSubstT(subst, replMap) & uniformSubstT(Substitution(Seq(new SubstitutionPair(aT, inst))), Map(repl(a, aX) -> repl(a, aX, atTrans = false))) &
                    (axiomT(axiomName) & alpha(AntePosition(0, HereP.first), aX) & AxiomCloseT))
                Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
              case None => println("Giving up " + this.name); None
            }
          case None => println("Giving up because the axiom does not exist " + this.name); None
        }

    }
  }

  /**
   * Creates a tactic to decompose quantifiers.
   * @return The tactic.
   */
  protected[tactics] def decomposeQuanT = new PositionTactic("Decompose Quantifiers") {
    override def applies(s: Sequent, pos: Position): Boolean = {
      var res = false
      val fn = new ExpressionTraversalFunction {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = if(p == pos.inExpr) Left(None) else Right(e)
        override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
          e match {
            case Forall(vars, f) if vars.length > 1 => res = true
            case Exists(vars, f) if vars.length > 1 => res = true
            case _ => res = false
          }
          Left(Some(new StopTraversal {}))
        }
      }
      ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fn), s(pos))
      res
    }

    override def apply(p: Position): Tactic = new ApplyRule(DecomposeQuantifiers(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }
}
