package edu.cmu.cs.ls.keymaera.tactics

// favoring immutable Seqs
import scala.collection.immutable.Seq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import scala.language.postfixOps
import edu.cmu.cs.ls.keymaera.core.PosInExpr

import EqualityRewritingImpl._
import PropositionalTacticsImpl._
import BranchLabels._

/**
 * In this object we collect wrapper tactics around the basic rules and axioms.
 *
 * Created by Jan-David Quesel on 4/28/14.
 * @author Jan-David Quesel
 * @author aplatzer
 */
object TacticLibrary {

  object TacticHelper {
    def getFormula(s: Sequent, p: Position): Formula = {
      require(p.inExpr == HereP)
      if(p.isAnte) s.ante(p.getIndex) else s.succ(p.getIndex)
    }
  }
  import TacticHelper._

  /*******************************************************************
   * Major tactics
   *******************************************************************/
 
  /**
   * Default tactics without any invariant generation.
   */
  def master = BuiltinHigherTactics.master _
  def default = BuiltinHigherTactics.master(new NoneGenerate(), exhaustive = true)
  def defaultNoArith = BuiltinHigherTactics.noArith(new NoneGenerate(), exhaustive = true)

  /**
   * Make a step in a proof at the given position (except when decision needed)
   */
  def step : PositionTactic = BuiltinHigherTactics.stepAt(beta = true, simplifyProg = true, quantifiers = true,
    equiv = true)

  /**
   * Tactic that applies propositional proof rules exhaustively.
   */
  // TODO Implement for real. This strategy uses more than propositional steps.
  def propositional = (closeT | locate(indecisive(true, false, false, true)))*

  def indecisive(beta: Boolean, simplifyProg: Boolean, quantifiers: Boolean, equiv: Boolean = false) =
    BuiltinHigherTactics.stepAt(beta, simplifyProg, quantifiers, equiv)

  /*******************************************************************
   * Arithmetic tactics
   *******************************************************************/

  /**
   * Tactic for arithmetic.
   * @return The tactic.
   */
  def arithmeticT = ArithmeticTacticsImpl.hideUnnecessaryLeftEqT ~
    ArithmeticTacticsImpl.quantifierEliminationT("Mathematica")

  /**
   * Quantifier elimination.
   */
  val quantifierEliminationT = ArithmeticTacticsImpl.quantifierEliminationT _

  /*******************************************************************
   * Elementary tactics
   *******************************************************************/

  /**
   * apply results in a formula to try.
   * Results do not have to be deterministic, e.g., calls to apply might advance to the next candidate.
   * Results can also be deterministic.
   */
  trait Generator[A] extends ((Sequent, Position) => Option[A]) {
    def peek(s: Sequent, p: Position): Option[A]
  }

  class Generate[A](f: A) extends Generator[A] {
    def apply(s: Sequent, p: Position) = Some(f)
    def peek(s: Sequent, p: Position) = Some(f)
  }

  class NoneGenerate[A] extends Generator[A] {
    def apply(s: Sequent, p: Position) = None
    def peek(s: Sequent, p: Position) = None
  }

  def universalClosure(f: Formula): Formula = {
    val vars = Helper.certainlyFreeNames(f)
    if(vars.isEmpty) f else Forall(vars.toList, f)
  }

//  def deskolemize(f : Formula) = {
//    val FV = SimpleExprRecursion.getFreeVariables(f)
//    Forall(FV, f)
//  }

  def decomposeQuanT = new PositionTactic("Decompose Quantifiers") {
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



  def onBranch(s: String, t: Tactic): Tactic = ifT(_.tacticInfo.infos.get("branchLabel") == Some(s), t)

  /**
   * used on line 236 to say "do equiv-r. On the left branch of that, do my
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
              require(candidates.length == 1, "There should be a unique branch with label " + l + " however there are " + candidates.length + " containing " + candidates.map(_._1))
              candidates.head._2
            }
        }
      })


  def lastSucc(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " succ.length - 1") {
    override def applicable(node: ProofNode): Boolean =
      pt.applies(node.sequent, SuccPosition(node.sequent.succ.length - 1))

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      Some(pt(SuccPosition(node.sequent.succ.length - 1)))
  }

  def lastAnte(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " ante.length - 1") {
    override def applicable(node: ProofNode): Boolean =
      pt.applies(node.sequent, AntePosition(node.sequent.ante.length - 1))

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      Some(pt(SuccPosition(node.sequent.ante.length - 1)))
  }

  def genInductionT(gen: Generator[Formula]): PositionTactic = new PositionTactic("Generate Invariant") {
    override def applies(s: Sequent, p: Position): Boolean = gen.peek(s, p) match {
      case Some(inv) => inductionT(Some(inv)).applies(s, p)
      case None => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = gen(node.sequent, p) match {
        case Some(inv) => Some(inductionT(Some(inv))(p))
        case None => None
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def inductionT(inv: Option[Formula]): PositionTactic = new PositionTactic("induction") {
    def getBody(g: Formula): Option[Program] = g match {
      case BoxModality(Loop(a), _) => Some(a)
      case _ => None
    }
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && getBody(s(p)).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def ind(cutSPos: Position, cont: Tactic) = boxInductionT(cutSPos) & AndRightT(cutSPos) & (LabelBranch("Close Next"), abstractionT(cutSPos) & hideT(cutSPos) & cont)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = inv match {
        case Some(f) =>
        val cutAPos = AntePosition(node.sequent.ante.length, HereP)
        val prepareKMP = new ConstructionTactic("Prepare K modus ponens") {
          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
            case x@BoxModality(a, _) =>
              val cPos = AntePosition(node.sequent.ante.length)
              val b1 = ImplyLeftT(cPos) & AxiomCloseT
              val b2 = hideT(p)
              Some(cutT(Some(Imply(BoxModality(a, f), x))) & onBranch((cutUseLbl, b1), (cutShowLbl, b2)))
            case _ => None
          }
          override def applicable(node: ProofNode): Boolean = true
        }
        val cutSPos = SuccPosition(node.sequent.succ.length - 1, HereP)
        val useCase = prepareKMP & hideT(cutAPos) & kModalModusPonensT(cutSPos) & abstractionT(cutSPos) & hideT(cutSPos) & LabelBranch(indUseCaseLbl)
        val branch1Tactic = ImplyLeftT(cutAPos) & (hideT(p) & LabelBranch(indInitLbl), useCase)
        val branch2Tactic = hideT(p) &
          ImplyRightT(cutSPos) &
          ind(cutSPos, hideT(cutAPos) & LabelBranch(indStepLbl)) &
          onBranch(("Close Next", AxiomCloseT))
        getBody(node.sequent(p)) match {
          case Some(a) =>
            Some(cutT(Some(Imply(f, BoxModality(Loop(a), f)))) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
          case None => None
        }
        case None => Some(ind(p, NilT) & LabelBranch(indStepLbl))
      }
    }
  }

  def abstractionT: PositionTactic = new PositionTactic("Abstraction") {
    override def applies(s: Sequent, p: Position): Boolean = p.inExpr == HereP && (s(p) match {
      case BoxModality(_, _) => true
      case DiamondModality(_, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(new AbstractionRule(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  /** *******************************************
    * Basic Tactics
    * *******************************************
    */

  val locateAnte = SearchTacticsImpl.locateAnte _
  val locateSucc = SearchTacticsImpl.locateSucc _

  /**
   * tactic locating an antecedent or succedent position where PositionTactic is applicable.
   */
  def locate(posT: PositionTactic): Tactic = locateSuccAnte(posT)

  /**
   * tactic locating an antecedent or succedent position where PositionTactic is applicable.
   */
  def locateAnteSucc(posT: PositionTactic): Tactic = locateAnte(posT) | locateSucc(posT)

  /**
   * tactic locating an succedent or antecedent position where PositionTactic is applicable.
   */
  def locateSuccAnte(posT: PositionTactic): Tactic = locateSucc(posT) | locateAnte(posT)

  def AndLeftT = PropositionalTacticsImpl.AndLeftT
  def AndRightT = PropositionalTacticsImpl.AndRightT
  def OrLeftT = PropositionalTacticsImpl.OrLeftT
  def OrRightT = PropositionalTacticsImpl.OrRightT
  def ImplyLeftT = PropositionalTacticsImpl.ImplyLeftT
  def ImplyRightT = PropositionalTacticsImpl.ImplyRightT
  def EquivLeftT = PropositionalTacticsImpl.EquivLeftT
  def EquivRightT = PropositionalTacticsImpl.EquivRightT
  def NotLeftT = PropositionalTacticsImpl.NotLeftT
  def NotRightT = PropositionalTacticsImpl.NotRightT

  // TODO get rid of those
  def AndLeftFindT: Tactic = locateAnte(AndLeftT)
  def AndRightFindT: Tactic = locateSucc(AndRightT)
  def OrLeftFindT: Tactic = locateAnte(OrLeftT)
  def OrRightFindT: Tactic = locateSucc(OrRightT)
  def ImplyLeftFindT: Tactic = locateAnte(ImplyLeftT)
  def ImplyRightFindT: Tactic = locateSucc(ImplyRightT)
  def EquivLeftFindT: Tactic = locateAnte(EquivLeftT)
  def EquivRightFindT: Tactic = locateSucc(EquivRightT)
  def NotLeftFindT: Tactic = locateAnte(NotLeftT)
  def NotRightFindT: Tactic = locateSucc(NotRightT)

  def hideT = PropositionalTacticsImpl.hideT
  def cutT(f: Option[Formula]): Tactic = PropositionalTacticsImpl.cutT((x: ProofNode) => f)

  def closeT : Tactic = AxiomCloseT | locateAnte(CloseTrueT) | locateSucc(CloseFalseT)
  def AxiomCloseT(a: Position, b: Position) = PropositionalTacticsImpl.AxiomCloseT(a, b)
  def AxiomCloseT = PropositionalTacticsImpl.AxiomCloseT
  def CloseTrueT = PropositionalTacticsImpl.CloseTrueT
  def CloseFalseT = PropositionalTacticsImpl.CloseFalseT


  
  /**
   * Axiom lookup imports an axiom into the antecedent.
   */
  def axiomT(id: String): Tactic = Axiom.axioms.get(id) match {
    case Some(_) => new Tactics.ApplyRule(Axiom(id)) {
      override def applicable(node: ProofNode): Boolean = true
    }
    case _ => throw new IllegalArgumentException("Unknown axiom " + id)
  }

  /**
   * Tactic to perform uniform substitution. In most cases this is called on a sequent that only contains a single
   * formula in order to show that a formula is an instance of an axiom (modulo an alpha renaming of that).
   *
   * @param subst the substitution to perform
   * @param delta a map with replacement for formulas in the sequent. That is, for all (f, g) in delta we will replace
   *              every top-level occurrence of formula f in the conclusion by the respective g
   *              in order to construct the origin of the uniform substitution.
   * @return an instance of a tactic that performs the given uniform substitution
   */
  def uniformSubstT(subst: Substitution, delta: (Map[Formula, Formula])): Tactic = new ConstructionTactic("Uniform Substitution") {
    def applicable(pn: ProofNode) = true

    def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = {
      val ante = for (f <- p.sequent.ante) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      val succ = for (f <- p.sequent.succ) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      Some(new Tactics.ApplyRule(UniformSubstitution(subst, Sequent(p.sequent.pref, ante, succ))) {
        override def applicable(node: ProofNode): Boolean = true
      })
    }

  }

  // axiom wrapper shell
  // TODO: Use findPosInExpr to find a position that matches the left side of the axiom and cut in the resulting instance
  // we start with just using findPos to get a top level position

  abstract class AxiomTactic(name: String, axiomName: String) extends PositionTactic(name) {
    val axiom = Axiom.axioms.get(axiomName)
    def applies(f: Formula): Boolean
    override def applies(s: Sequent, p: Position): Boolean = axiom.isDefined && applies(getFormula(s, p))

    /**
     * This methods constructs the axiom before the renaming, axiom instance, substitution to be performed and a tactic
     * that performs the renaming.
     *
     * An axiom tactic performs the following steps (Hilbert style):
     * 1. Guess axiom
     * 2. Rename bound variables to match the instance we want
     * 3. Perform Uniform substitution to instantiate the axiom
     *
     * Axioms usually have the form ax = OP(a, b). The constructed instance either has the form OP(f, g) or OP(g, f).
     * Here, f is an input to this function and g is derived from the axiom to be used. The output of this function
     * should be 4 things:
     * 1. The form of the axiom before apply the tactic provided in 4
     * 2. The instance of the axiom eventually to be used in the proof
     * 3. The substitution to turn 2 into 1
     * 4. A tactic to turn the result of 3 into the actual axiom
     *
     * In the long run all this should be computed by unification.
     *
     * @param f the formula that should be rewritten using the axiom
     * @param ax the axiom to be used
     * @param pos the position to which this rule is applied to
     * @return (Axiom before executing the given position tactic;
     *         the instance of the axiom,
     *         the uniform substitution that transforms the first into the second axiom (Hilbert style);
     *         an optional position tactic that transforms the first
     *         argument into the actual axiom (usually alpha renaming)).
     * @see #constructInstanceAndSubst(Formula)
     */
    def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      constructInstanceAndSubst(f, ax)

    def constructInstanceAndSubst(f: Formula, ax: Formula): Option[(Formula, Formula, Substitution, Option[PositionTactic])] = {
      constructInstanceAndSubst(f) match {
        case Some((instance, subst)) => Some((ax, instance, subst, None))
        case None => None
      }
    }

    /**
     * This is a simpler form of the constructInstanceAndSubst method. It just gets the formula to be rewritten
     * and has to construct the axiom instance and the substitution to transform the axiom into its instance.
     *
     * This method will be called by the default implementation of constructInstanceAndSubst(f: Formula, a: Formula).
     *
     * @param f The formula to be rewritten using an axiom
     * @return (The axiom instance to be constructed and used for rewriting;
     *          Substitution to transform the axiom into its instance)
     * @see #constructInstanceAndSubst(Formula,Formula)
     */
    def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = ???

    //@TODO Add contract that applies()=>\result fine
    override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        axiom match {
          case Some(ax) =>
            constructInstanceAndSubst(getFormula(node.sequent, pos.topLevel), ax, pos) match {
              case Some((ax, axiomInstance, subst, ptac)) =>
              {
                val axiomInstPos = AntePosition(node.sequent.ante.length)
                val axiomApplyTactic = assertPT(axiomInstance)(axiomInstPos) & (axiomInstance match {
                  //@TODO Prefer simpler sequent proof rule for <->left rather than congruence rewriting if the position to use it on is on top-level of sequent
                  //@TODO If Pos.isAnte the following position management seems wrong since unstable.
                  case Equiv(_, _) => equalityRewriting(axiomInstPos, pos) & ((assertPT(axiomInstance)&hideT)(axiomInstPos) & (assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos.topLevel))
                  case Equals(Real, _, _) => equalityRewriting(axiomInstPos, pos, false) & ((assertPT(axiomInstance)&hideT)(axiomInstPos) & (assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos.topLevel))
                  case Imply(_, _) if(pos.isAnte  && pos.inExpr == HereP) => modusPonensT(pos, axiomInstPos)
                  case Imply(_, _) if(!pos.isAnte && pos.inExpr == HereP) => ImplyLeftT(axiomInstPos) & ((assertPT(node.sequent(pos),"hiding original instance")&hideT)(pos), AxiomCloseT(axiomInstPos.topLevel, pos))
                  case _ => ???
                })
                // // hide in reverse order since hiding changes positions
                // val hideAllAnte = for(i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                // val hideAllSuccButLast = for(i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                // val hideAllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
                //@TODO Insert contract tactic after hiding all which checks that exactly the intended axiom formula remains and nothing else.
                //@TODO Introduce a reusable tactic that hides all formulas except the ones given as argument and is followed up by a contract ensuring that exactly those formuals remain.
                val cont = ptac match {
                  // SuccPosition(0) is the only position remaining in axiom proof
                  case Some(tactic) => assertT(0, 1) & tactic(SuccPosition(0))
                  case None => NilT
                }
                val axiomPos = SuccPosition(node.sequent.succ.length)
                println("Axiom instance " + axiomInstance)
                val axiomInstanceTactic = (assertPT(axiomInstance) & cohideT)(axiomPos) & (assertT(0,1) & assertT(axiomInstance, SuccPosition(0)) & uniformSubstT(subst, Map(axiomInstance -> ax)) & assertT(0, 1) & (cont & axiomT(axiomName) & assertT(1,1) & AxiomCloseT))
                Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, axiomApplyTactic), (cutShowLbl, axiomInstanceTactic)))
               }
              case None => None
            }
          case None => None
        }
      }
    }

  }

  def equalityRewriting(eqPos: Position, p: Position, checkDisjoint: Boolean = true) =
    EqualityRewritingImpl.equalityRewriting(eqPos, p, checkDisjoint)
  def equalityRewritingLeft(eqPos: Position) = EqualityRewritingImpl.equalityRewritingLeft(eqPos)
  def equalityRewritingRight(eqPos: Position) = EqualityRewritingImpl.equalityRewritingRight(eqPos)


  val uniquify = new PositionTactic("Uniquify") {
    // for now only on top level
    def getBoundVariables(s: Sequent, p: Position): Option[Seq[(String, Option[Int])]] = s(p) match {
        case Forall(v, _) => Some(v.map(_ match {
          case Variable(n, i, _) => (n, i)
          case _ => ???
        }))
        case Exists(v, _) => Some(v.map(_ match {
          case Variable(n, i, _) => (n, i)
          case _ => ???
        }))
        case BoxModality(Assign(Variable(name, i, _), e), _) => Some(Seq((name, i)))
        case BoxModality(NDetAssign(Variable(name, i, _)), _) => Some(Seq((name, i)))
        case DiamondModality(Assign(Variable(name, i, _), e), _) => Some(Seq((name, i)))
        case DiamondModality(NDetAssign(Variable(name, i, _)), _) => Some(Seq((name, i)))
        case a => None
      }
    override def applies(s: Sequent, p: Position): Boolean = (p.inExpr == HereP) && getBoundVariables(s, p).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        getBoundVariables(node.sequent, p) match {
          case Some(s) =>
            var otherVars = (Helper.namesIgnoringPosition(node.sequent, p).map((n: NamedSymbol) => (n.name, n.index)) ++ s)
            val res: Seq[Option[Tactic]] = for((n, idx) <- s) yield {
              val vars = otherVars.filter(_._1 == n)
              //require(vars.size > 0, "The variable we want to rename was not found in the sequent all together " + n + " " + node.sequent)
              // we do not have to rename if there are no name clashes
              if (vars.size > 0) {
                val maxIdx: Option[Int] = vars.map(_._2).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) => acc match {
                  case Some(a) => i match {
                    case Some(b) => if (a < b) Some(b) else Some(a)
                    case None => Some(a)
                  }
                  case None => i
                })
                val tIdx: Option[Int] = maxIdx match {
                  case None => Some(0)
                  case Some(a) => Some(a + 1)
                }
                otherVars = otherVars ++ Seq((n, tIdx))
                Some(alphaRenamingT(n, idx, n, tIdx)(p))
              } else {
                None
              }
            }
            val tactic = res.flatten.reduceRight(seqT)
            Some(tactic)
          case None => None
        }
      }
    }

  }

  // assignment tactic (alpha renaming and then assignment rule)

  // it would be great if we could access the same position to apply the imply right rule
  // FIXME: this only works for toplevel positions since there the positions are stable
  private def assignmentFindImpl = locateSucc(assignment & ImplyRightT) | locateAnte(assignment & ImplyLeftT)

  val assignment = new PositionTactic("Assignment") {
    // for now only on top level
    override def applies(s: Sequent, p: Position): Boolean = {
      (p.inExpr == HereP) && ((if (p.isAnte) s.ante else s.succ)(p.index) match {
        case BoxModality(Assign(Variable(_, _, _), _), _) => true
        case DiamondModality(Assign(Variable(_, _, _), _), _) => true
        case _ => false
      })
    }

    override def apply(p: Position): Tactic = Tactics.weakSeqT(uniquify(p), new ApplyRule(new AssignmentRule(p)) {
      override def applicable(n: ProofNode): Boolean = applies(n.sequent, p)
    })
  }
  
  // axiom wrappers

  // axiomatic version of assignment axiom assignaxiom
  val assignT = boxAssignT /*@TODO | diamondAssignT*/
  val boxAssignT = HybridProgramTacticsImpl.boxAssignT




  def findPosInExpr(s: Sequent, blacklist: Set[NamedSymbol], search: Expr, ignore: Position): Option[Position] =
    findPosInExpr(s, blacklist, search == _, Some(ignore))

  def findPosInExpr(s: Sequent, blacklist: Set[NamedSymbol], test: (Expr => Boolean), filterPos: Option[Position]): Option[Position] = {
    var posInExpr: PosInExpr = null
    val f = new ExpressionTraversalFunction {
      val stop = new StopTraversal {}

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = if (test(e)) {
        posInExpr = p
        Left(Some(stop))
      } else {
        e match {
          case Forall(v, phi) if (blacklist.map(v.contains).foldLeft(false)(_ || _)) => Left(Some(stop))
          case Exists(v, phi) if (blacklist.map(v.contains).foldLeft(false)(_ || _)) => Left(Some(stop))
          case BoxModality(a, c) if (blacklist.map(a.writes.contains).foldLeft(false)(_ || _)) => Left(Some(stop))
          case DiamondModality(a, c) if (blacklist.map(a.writes.contains).foldLeft(false)(_ || _)) => Left(Some(stop))
          case _ => Left(None)
        }
      }

      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = if (test(e)) {
        posInExpr = p
        Left(Some(stop))
      } else Left(None)

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        if (test(e)) {
          posInExpr = p
          Left(Some(stop))
        } else Left(None)
      }


      override def preG(p: PosInExpr, e: ModalOp): Either[Option[StopTraversal], ModalOp] = if (test(e)) {
          posInExpr = p
          Left(Some(stop))
        } else Left(None)

    }
    val ignore = filterPos match {
      case Some(p) => p
      case None => null
    }
    for(i <- 0 until s.ante.length) {
      if(ignore == null || !ignore.isAnte || ignore.getIndex != i) {
        ExpressionTraversal.traverse(f, s.ante(i))
        if (posInExpr != null) {
          return Some(AntePosition(i, posInExpr))
        }
      }
    }
    for(i <- 0 until s.succ.length) {
      if(ignore == null || ignore.isAnte || ignore.getIndex != i) {
        ExpressionTraversal.traverse(f, s.succ(i))
        if (posInExpr != null) {
          return Some(SuccPosition(i, posInExpr))
        }
      }
    }
    None
  }

  def findPosInExpr(left: Boolean, s: Sequent, eqPos: Position): Option[Position] = {
    val eq = s.ante(eqPos.getIndex)
    val blacklist = Helper.names(eq)
    val search: Expr = eq match {
      case Equals(_, a, b) => if(left) a else b
      case ProgramEquals(a, b) => if(left) a else b
      case Equiv(a, b) => if(left) a else b
      case _ => throw new IllegalArgumentException("Equality Rewriting does not work for " + eq)
    }
    findPosInExpr(s, blacklist, search, eqPos)
  }

  def eqRewritePos(left: Boolean, eqPos: Position): Tactic = new ConstructionTactic("Apply Equality Left") {
    require(eqPos.isAnte && eqPos.inExpr == HereP, "Equalities for rewriting have to be in the antecedent")

    override def applicable(node: ProofNode): Boolean = findPosInExpr(left, node.sequent, eqPos).isDefined

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      findPosInExpr(left, node.sequent, eqPos) match {
        case Some(p) =>
          val t = equalityRewriting(eqPos, p)
          val hide = hideT(p.topLevel)
          Some(t & hide)
        case None => None
      }
    }
  }

  def eqLeft(exhaustive: Boolean): PositionTactic = new PositionTactic("Find Equality and Apply Right to Left") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && isEquality(s, p, true) && findPosInExpr(true, s, p).isDefined

    override def apply(p: Position): Tactic = if(exhaustive) eqRewritePos(true, p)* else eqRewritePos(true, p)
  }

  val eqLeftFind = locateAnte(eqLeft(false))

  val eqLeftFindExhaustive = locateAnte(eqLeft(true))

  def eqRight(exhaustive: Boolean): PositionTactic = new PositionTactic("Find Equality and Apply Left to Right") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && isEquality(s, p, true) && findPosInExpr(false, s, p).isDefined

    override def apply(p: Position): Tactic = if(exhaustive) eqRewritePos(false, p)* else eqRewritePos(false, p)
  }

  val eqRightFind = locateAnte(eqRight(false))

  val eqRightFindExhaustive = locateAnte(eqRight(true))

  def debugT(s: String): Tactic = new Tactic("Debug") {
    override def applicable(node: ProofNode): Boolean = true

    override def apply(tool: Tool, node: ProofNode): Unit = {
      println("===== " + s + " ==== " + node.sequent + " =====")
      continuation(this, Success, Seq(node))
    }
  }

  val boxTestT = HybridProgramTacticsImpl.boxTestT
  val boxNDetAssign = HybridProgramTacticsImpl.boxNDetAssign
  val boxSeqT = HybridProgramTacticsImpl.boxSeqT
  val boxInductionT = HybridProgramTacticsImpl.boxInductionT
  val boxChoiceT = HybridProgramTacticsImpl.boxChoiceT



  def modusPonensT(assumption: Position, implication: Position): Tactic = new ConstructionTactic("Modus Ponens") {
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val p = AntePosition(assumption.getIndex - (if(assumption.getIndex > implication.getIndex) 1 else 0))
      Some(ImplyLeftT(implication) & (AxiomCloseT(p, SuccPosition(node.sequent.succ.length)), hideT(assumption)))
    }

    override def applicable(node: ProofNode): Boolean = assumption.isAnte && implication.isAnte &&
      ((getFormula(node.sequent, assumption), getFormula(node.sequent, implication)) match {
      case (a, Imply(b, c)) if (a == b) => true
      case (a, b) => false
    })
  }

  def alphaRenamingT(from: String, fromIdx: Option[Int], to: String, toIdx: Option[Int]): PositionTactic =
    new PositionTactic("Alpha Renaming") {
      override def applies(s: Sequent, p: Position): Boolean = true // @TODO: really check applicablity

      override def apply(p: Position): Tactic = (new ApplyRule(new AlphaConversion(p, from, fromIdx, to, toIdx)) {
        override def applicable(node: ProofNode): Boolean = true
        } & hideT(p.topLevel))
  }

  // Quantifier Instantiation
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
          case Forall(v, f) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), f))
          case Exists(v, f) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) { require(n.isInstanceOf[NamedSymbol]); n.asInstanceOf[NamedSymbol] } else name ), f))
          case _ => Left(None)
        }
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
      }, f) match {
        case Some(g) => g
        case None => throw new IllegalStateException("Replacing one variable by another should not fail")
      }

      def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution, (Variable, Variable), (Term, Variable))] = f match {
        case Forall(x, qf) if (x.contains(quantified)) =>
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
        case Forall(x, qf) if (!x.contains(quantified)) =>
          println(x + " does not contain " + quantified)
          x.map(_ match {
            case x: NamedSymbol => println("Symbol " + x.name + " " + x.index)
            case _ =>
          })
          None
        case _ =>
          println("Cannot instantiate quantifier for " + quantified.prettyString() + " in " + f.prettyString())
          None
      }

      def decompose(d: Formula): Formula = d match {
        case Forall(v, f) if(v.length > 1) => Forall(v.take(1), Forall(v.drop(1), f))
        case Exists(v, f) if(v.length > 1) => Exists(v.take(1), Exists(v.drop(1), f))
        case _ => d
      }

      // since we have an implication, we use modus ponens to get it's consequence
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        axiom match {
          case Some(a) =>
            constructInstanceAndSubst(getFormula(node.sequent, pos)) match {
              case Some((axiomInstance, subst, (quantified, aX), (instance, aT))) =>
                val eqPos = AntePosition(node.sequent.ante.length)
                val branch1Tactic = modusPonensT(pos, eqPos)
                // val hideAllAnte = for (i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                // val hideAllSuccButLast = for (i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                // val hideSllAnteAllSuccButLast = (hideAllAnte ++ hideAllSuccButLast).reduce(seqT)
                def alpha(p: Position, q: Variable) = alphaRenamingT(q.name, q.index, "$" + aX.name, aX.index)(p)
                def repl(f: Formula, v: Variable, atTrans: Boolean = true):Formula = f match {
                  case Imply (a, b) => Imply(decompose(replace (a)(v, Variable ("$" + aX.name, aX.index, aX.sort) )), if(atTrans) replace(b)(aT, instance) else b)
                  case _ => throw new IllegalArgumentException("...")
                }
                val replMap = Map(repl(axiomInstance, quantified, false) -> repl(a, aX))
                val branch2Tactic = (cohideT(SuccPosition(node.sequent.succ.length)) ~
                  alpha(SuccPosition(0, HereP.first), quantified) ~
                  decomposeQuanT(SuccPosition(0, HereP.first)) ~
                  (uniformSubstT(subst, replMap) & uniformSubstT(Substitution(Seq(new SubstitutionPair(aT, instance))), Map(repl(a, aX) -> repl(a, aX, false))) &
                    (axiomT(axiomName) & alpha(AntePosition(0, HereP.first), aX) & AxiomCloseT)))
                Some(cutT(Some(axiomInstance)) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
              case None => println("Giving up " + this.name); None
            }
          case None => println("Giving up because the axiom does not exist " + this.name); None
        }

    }
  }

  // K modal  modus ponens
  def kModalModusPonensT = new AxiomTactic("K modal modus ponens", "K modal modus ponens") {
    override def applies(f: Formula): Boolean = f match {
      case Imply(BoxModality(a, _), BoxModality(b, _)) if(a == b) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case Imply(BoxModality(a, p), BoxModality(b, q)) if(a == b) =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aP = PredicateConstant("p")
        val aQ = PredicateConstant("q")
        val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aP, p), new SubstitutionPair(aQ, q))
        // construct axiom instance: [a](p->q) -> (([a]p) -> ([a]q))
        val g = BoxModality(a, Imply(p, q))
        val axiomInstance = Imply(g, f)
        Some(axiomInstance, Substitution(l))
      case _ => None
    }
  }



  def skolemizeT = new PositionTactic("Skolemize") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case Forall(_, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(uniquify(p) ~ new ApplyRule(new Skolemize(p)) {
          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        })
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def diffCutT(h: Formula): PositionTactic = new PositionTactic("Differential cut with " + h.prettyString()) {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case BoxModality(ContEvolve(_), _) => true
      case BoxModality(_: NFContEvolve, _) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ApplyRule(new DiffCut(p, h)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def differentialInduction: PositionTactic = new PositionTactic("Perform differential induction") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case Some(BoxModality(ContEvolve(_), _)) => true
      case Some(BoxModality(_: NFContEvolve, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(diffIndT(p) & abstractionT(p) & skolemizeT(p) & ImplyRightT(p) & deriveFormulaT(p))
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def diffIndT: PositionTactic = new PositionTactic("Differential Induction") {

    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case Some(BoxModality(ContEvolve(_), _)) => true
      case Some(BoxModality(_: NFContEvolve, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ApplyRule(new DiffInd(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveFormulaT: PositionTactic = new PositionTactic("Derive Formula") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case Some(FormulaDerivative(_)) => true
      case Some(a) => println("Not applicable to " + a.prettyString); false
      case None => println("Not applicable to None"); false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        println("Constructing at " + p);
        Retrieve.formula(node.sequent, p) match {
          case Some(FormulaDerivative(And(_, _))) => Some(deriveAndT(p) ~ deriveFormulaT(p.first) ~ deriveFormulaT(p.second))
          case Some(FormulaDerivative(Or(_, _))) => Some(deriveOrT(p) ~ deriveFormulaT(p.first) ~ deriveFormulaT(p.second))
          case Some(FormulaDerivative(Equals(Real, _, _))) => println("found equals"); Some(deriveEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(NotEquals(Real, _, _))) => Some(deriveNotEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(GreaterThan(Real, _, _))) => Some(deriveGreaterThanT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(GreaterEqual(Real, _, _))) => Some(deriveGreaterEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(LessThan(Real, _, _))) => Some(deriveLessThanT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(LessEqual(Real, _, _))) => Some(deriveLessEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveTermT: PositionTactic = new PositionTactic("Derive Term") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.term(s, p) match {
      case Some(Derivative(_, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        println("Checking " + Retrieve.term(node.sequent, p))
        Retrieve.term(node.sequent, p) match {
          case Some(Derivative(Real, Neg(Real, _))) => Some(deriveNegT(p) ~ deriveTermT(p.first))
          case Some(Derivative(Real, Add(Real, _, _))) => println("Found sum"); Some(deriveSumT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(Derivative(Real, Subtract(Real, _, _))) => Some(deriveMinusT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(Derivative(Real, Multiply(Real, _, _))) => Some(deriveProductT(p) ~ deriveTermT(p.first.first) ~ deriveTermT(p.second.second))
          case Some(Derivative(Real, Divide(Real, _, _))) => Some(deriveQuotientT(p) ~ deriveTermT(p.first.first) ~ deriveTermT(p.second.second))
          case Some(Derivative(Real, Exp(Real, Variable(_,_,Real), Number(Real, _)))) => Some(deriveMonomialT(p))
          case Some(Derivative(Real, Number(Real, _))) => Some(deriveConstantT(p))
          case _ => println("Don't know what to do"); None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveAndT: PositionTactic = new AxiomTactic("&' derive and", "&' derive and") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(And(_, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(And(p, q))) =>
        // construct substitution
        val aP = PredicateConstant("p")
        val aQ = PredicateConstant("q")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aQ, q))
        val g = And(FormulaDerivative(p), FormulaDerivative(q))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }  }

  def deriveOrT: PositionTactic = new AxiomTactic("|' derive or", "|' derive or") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(Or(_, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(Or(p, q))) =>
        // construct substitution
        val aP = PredicateConstant("p")
        val aQ = PredicateConstant("q")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aQ, q))
        val g = And(FormulaDerivative(p), FormulaDerivative(q))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  def deriveEqualsT: PositionTactic = new AxiomTactic("=' derive =", "=' derive =") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(Equals(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(Equals(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = Equals(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  def deriveNotEqualsT: PositionTactic = new AxiomTactic("!=' derive !=", "!=' derive !=") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(NotEquals(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(NotEquals(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = Equals(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  def deriveGreaterEqualsT: PositionTactic = new AxiomTactic(">=' derive >=", ">=' derive >=") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(GreaterEqual(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(GreaterEqual(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = GreaterEqual(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  def deriveGreaterThanT: PositionTactic = new AxiomTactic(">' derive >", ">' derive >") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(GreaterThan(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(GreaterThan(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = GreaterEqual(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equiv(f, g)
          Some(ax, axiomInstance, Substitution(l), None)
        case _ => None
      }
  }

   def deriveLessEqualsT: PositionTactic = new AxiomTactic("<=' derive <=", "<=' derive <=") {
     def applies(f: Formula) = ???
     override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(LessEqual(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(LessEqual(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = LessEqual(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None)
      case _ => None
    }
  }

  def deriveLessThanT: PositionTactic = new AxiomTactic("<' derive <", "<' derive <") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(LessThan(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(LessThan(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = LessEqual(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equiv(f, g)
          Some(ax, axiomInstance, Substitution(l), None)
        case _ => None
      }
  }

  def deriveNegT: PositionTactic = new AxiomTactic("-' derive neg", "-' derive neg") {
     def applies(f: Formula) = ???
     override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
       case Some(Derivative(Neg(Real, _))) => true
       case _ => false
     })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Neg(Real, s))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val l = List(new SubstitutionPair(aS, s))
          val g = Neg(Real, Derivative(Real, s))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None)
        case _ => None
    }
  }

   def deriveSumT: PositionTactic = new AxiomTactic("+' derive sum", "+' derive sum") {
     def applies(f: Formula) = ???
     override def applies(s: Sequent,p:Position): Boolean = {
       axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
         case Some(Derivative(Real, Add(Real, _, _))) => true
         case _ => false
       })
     }

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Add(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Add(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None)
        case _ => println("Not applicable deriveSumT to " + in.prettyString() + " at " + pos); None
    }
  }

  def deriveMinusT: PositionTactic = new AxiomTactic("-' derive minus", "-' derive minus") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Subtract(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Subtract(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Subtract(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None)
        case _ => None
      }
  }

   def deriveProductT: PositionTactic = new AxiomTactic("*' derive product", "*' derive product") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Multiply(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Multiply(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Add(Real, Multiply(Real, Derivative(Real, s), t), Multiply(Real, s, Derivative(Real, t)))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None)
        case _ => None
    }
  }

  def deriveQuotientT: PositionTactic = new AxiomTactic("/' derive quotient", "/' derive quotient") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Divide(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula, Substitution, Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Divide(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Divide(Real, Subtract(Real, Multiply(Real, Derivative(Real, s), t), Multiply(Real, s, Derivative(Real, t))), Exp(Real, t, Number(2)))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None)
        case _ => None
    }
  }
  def deriveMonomialT: PositionTactic = new PositionTactic("Derive Monomial") {
    override def applies(s: Sequent,p:Position): Boolean = Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Exp(Real, Variable(_,_,Real), Number(Real,_)))) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Retrieve.subTerm(node.sequent(p), p.inExpr) match {
          case Some(f@Derivative(Real, Exp(Real, Variable(_,_,Real), Number(Real,_)))) =>
            val app = new ApplyRule(DeriveMonomial(f)) {
              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
            val eqPos = AntePosition(node.sequent.ante.length)
            Some(app & equalityRewriting(eqPos, p, false) & hideT(p.topLevel) & hideT(eqPos))
          case None => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveConstantT: PositionTactic = new PositionTactic("Derive Constant") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Number(_, _))) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Retrieve.subTerm(node.sequent(p), p.inExpr) match {
          case Some(f@Derivative(Real, num@Number(Real, n))) =>
            val app = new ApplyRule(DeriveConstant(f)) {
              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
            val eqPos = AntePosition(node.sequent.ante.length)
            Some(app & equalityRewriting(eqPos, p) & hideT(p.topLevel) & hideT(eqPos))
          case None => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  object Retrieve {
    val stop = Left(Some(new StopTraversal {}))
    def formula(s: Sequent, p: Position): Option[Formula] = subFormula(s(p), p.inExpr)

    def subFormula(in: Formula, inExpr: PosInExpr): Option[Formula] =
      if(inExpr == HereP) Some(in) else {
        var f: Option[Formula] = None
        ExpressionTraversal.traverse(TraverseToPosition(inExpr, new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = { f = Some(e); stop }
        }), in)
        f
      }

    def term(s: Sequent, p: Position): Option[Term] = subTerm(s(p), p.inExpr)

    def subTerm(f: Formula, inExpr: PosInExpr): Option[Term] = {
      var t: Option[Term] = None
      ExpressionTraversal.traverse(TraverseToPosition(inExpr, new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = { t = Some(e); stop }
      }), f)
      t
    }
  }
}
