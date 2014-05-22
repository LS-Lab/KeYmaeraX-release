package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import scala.Unit
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import scala.language.postfixOps
import scala.Some
import edu.cmu.cs.ls.keymaera.core.PosInExpr

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
   * Default tactic without any invariant generation.
   */
  def default = master(new NoneGenerate(), true)
  
  /**
   * Master tactic
   */
  def master(invGenerator: Generator[Formula], exhaustive: Boolean = false) = {
    def repeat(t: Tactic):Tactic = if(exhaustive) repeatT(t) else t
    repeat(closeT
      | locateSuccAnte(indecisive(false, true, true))
      | locateSuccAnte(indecisive(true, true, true))
      | locateSucc(genInductionT(invGenerator))
      | eqLeftFind
    ) ~ arithmeticT
  }

  /**
   * Make a step in a proof at the given position (except when decision needed)
   */
  def step : PositionTactic = indecisive(true, true, true, true)

  /**
   * Tactic that applies propositional proof rules exhaustively.
   *@TODO Implement for real. This strategy uses more than propositional steps.
   */
  def propositional = ((closeT | locate(indecisive(true, false, false, true)))*)


  /**
   * Tactic for arithmetic
   * @return
   */
  def arithmeticT = hideUnnecessaryLeftEqT ~ quantifierEliminationT("Mathematica")

  def hideUnnecessaryLeftEqT: Tactic = new ConstructionTactic("Hide Equations") {
    import Helper.names
    def collectEquations(s: Sequent): Seq[(Int, Term, Term)] =
      (for(i <- 0 until s.ante.length)
        yield s.ante(i) match {
          case Equals(_, a, b) if(names(a).intersect(names(b)).isEmpty) => Some((i, a, b))
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

  /**
   * Tactics for real arithmetic
   */
  
  def desequentialization(s : Sequent) = {
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

  def universalClosure(f: Formula): Formula = Forall(Helper.certainlyFreeNames(f).toList, f)

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

  def quantifierEliminationT(toolId: String): Tactic = new Tactic("Quantifier Elimination") {
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
                  val contTactic = ((closeT | locateSucc(indecisive(true, false, true)) | locateAnte(indecisive(true, false, true, true)))*)
                  def branch1(inst: Tactic): Tactic = AndLeftT(pos) & hideT(pos + 1) & inst & contTactic
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

  def onBranch(s: String, t: Tactic): Tactic = ifT(_.info.branchLabel == s, t)

  def onBranch(s1: (String, Tactic), spec: (String, Tactic)*): Tactic =
    if(spec.isEmpty)
     ifT(_.info.branchLabel == s1._1, s1._2)
    else
      switchT((pn: ProofNode) => {
        val candidates = (s1 +: spec).filter((s: (String, Tactic)) => pn.info.branchLabel == s._1)
        if(candidates.isEmpty) NilT
        else {
          require(candidates.length == 1)
          candidates.head._2
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
        case Some(inv) => Some((inductionT(Some(inv))(p)))
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
              Some(cutT(Imply(BoxModality(a, f), x)) & onBranch((cutUseLbl, b1), (cutShowLbl, b2)))
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
            Some(cutT(Imply(f, BoxModality(Loop(a), f))) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
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

  /**
   * tactic locating an antecedent position where PositionTactic is applicable.
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
      return None
    }
  }

  /**
   * tactic locating a succedent position where PositionTactic is applicable.
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
      return None
    }
  }

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

  def AndLeftT: PositionTactic = new PositionTactic("AndLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AndLeftFindT: Tactic = locateAnte(AndLeftT)

  def AndRightT: PositionTactic = new PositionTactic("AndRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AndRightFindT: Tactic = locateSucc(AndRightT)

  def OrLeftT: PositionTactic = new PositionTactic("OrLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrLeftFindT: Tactic = locateAnte(OrLeftT)

  def OrRightT: PositionTactic = new PositionTactic("OrRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrRightFindT: Tactic = locateSucc(OrRightT)

  def ImplyLeftT: PositionTactic = new PositionTactic("ImplyLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Imply(_, _) => p.inExpr == HereP
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyLeftFindT: Tactic = locateAnte(ImplyLeftT)

  def ImplyRightT: PositionTactic = new PositionTactic("ImplyRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && p.inExpr == HereP && (s.succ(p.index) match {
      case Imply(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyRightFindT: Tactic = locateSucc(ImplyRightT)

  def EquivLeftT: PositionTactic = new PositionTactic("EquivLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Equiv(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(EquivLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(equivLeftLbl), LabelBranch(equivRightLbl))
  }

  def EquivLeftFindT: Tactic = locateAnte(EquivLeftT)

  def EquivRightT: PositionTactic = new PositionTactic("EquivRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && (s.succ(p.index) match {
      case Equiv(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(EquivRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    } & (LabelBranch(equivLeftLbl), LabelBranch(equivRightLbl))
  }

  def EquivRightFindT: Tactic = locateSucc(EquivRightT)

  def NotLeftT: PositionTactic = new PositionTactic("NotLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def NotLeftFindT: Tactic = locateAnte(NotLeftT)

  def NotRightT: PositionTactic = new PositionTactic("NotRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def NotRightFindT: Tactic = locateSucc(NotRightT)

  def hideT: PositionTactic = new PositionTactic("Hide") {
    def applies(s: Sequent, p: Position) = true

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(if (pos.isAnte) HideLeft(pos) else HideRight(pos)) {
      override def applicable(node: ProofNode): Boolean = true
    }
  }

  def cutT(g: (ProofNode => Option[Formula])): Tactic = new ConstructionTactic("Cut") {
    def applicable(pn: ProofNode): Boolean = g(pn) match {
      case Some(_) => true
      case _ => false
    }

    override def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = g(p) match {
      case Some(t) =>
        Some(new Tactics.ApplyRule(Cut(t)) {
          override def applicable(node: ProofNode): Boolean = true
        } & (LabelBranch(BranchLabels.cutUseLbl), LabelBranch(BranchLabels.cutShowLbl)))
      case _ => None
    }
  }

  def cutT(f: Formula): Tactic = cutT((x: ProofNode) => Some(f))

  def closeT : Tactic = AxiomCloseT | locateAnte(CloseTrueT) | locateSucc(CloseFalseT)

  def AxiomCloseT(a: Position, b: Position): Tactic = new Tactics.ApplyRule(AxiomClose(a, b)) {
      override def applicable(node: ProofNode): Boolean = a.isAnte && !b.isAnte && getFormula(node.sequent, a) == getFormula(node.sequent, b)
  }

  def AxiomCloseT: Tactic = new ConstructionTactic("AxiomClose") {
    def constructTactic(tool: Tool, p: ProofNode): Option[Tactic] = findPositions(p.sequent) match {
      case Some((a, b)) => Some(AxiomCloseT(a, b))
      case None => None
    }

    def findPositions(s: Sequent): Option[(Position, Position)] = {
      for (f <- s.ante; g <- s.succ)
        if (f == g) return Some((AntePosition(s.ante.indexOf(f)), SuccPosition(s.succ.indexOf(g))))
      None
    }

    override def applicable(node: ProofNode): Boolean = findPositions(node.sequent) match {
      case Some(_) => true
      case _ => false
    }
  }

  def CloseTrueT: PositionTactic = new PositionTactic("CloseTrue") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && (getFormula(s, p) match {
      case True() => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(CloseTrue(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }
  def CloseFalseT: PositionTactic = new PositionTactic("CloseFalse") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (getFormula(s, p) match {
      case False() => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(CloseFalse(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }
  
  // Axiom lookup
  def axiomT(id: String): Tactic = Axiom.axioms.get(id) match {
    case Some(_) => new Tactics.ApplyRule(Axiom(id)) {
      override def applicable(node: ProofNode): Boolean = true
    }
    case _ => throw new IllegalArgumentException("Unknown axiom " + id)
  }

  //@TODO Document
  def uniformSubstT(subst: Substitution, delta: (Map[Formula, Formula])) = new ConstructionTactic("Uniform Substitution") {
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

  // assignment tactic (alpha renaming and then assignment rule)
  def assignmentFindAnte = locateAnte(assignment)
  def assignmentFindSucc = locateSucc(assignment)
  def assignmentFind = assignmentFindSucc | assignmentFindAnte
  // it would be great if we could access the same position to apply the imply right rule
  // FIXME: this only works for toplevel positions since there the positions are stable
  def assignmentFindImpl = locateSucc(assignment & ImplyRightT) | locateAnte(assignment & ImplyLeftT)

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
  
  // axiomatic version of assignment axiom assignaxiom
  val assignT = boxAssignT /*@TODO | diamondAssignT*/
  
  // axiomatic assignequal
  def boxAssignT: PositionTactic = new AxiomTactic("[:=] assignment equal", "[:=] assignment equal") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Assign(Variable(_, _,_), _), _) => true
      case _ => false
    }

    def replace(f: Formula)(o: Variable, n: Variable): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case Forall(v, f) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) n else name ), f))
        case Exists(v, f) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) n else name ), f))
        case BoxModality(Assign(x: Variable, t), p) => if(x == o) Right(BoxModality(Assign(n, t), p)) else Right(e)
        case DiamondModality(Assign(x: Variable, t), p) => if(x == o) Right(DiamondModality(Assign(n, t), p)) else Right(e)
        case _ => Left(None)
      }
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
    }, f) match {
      case Some(g) => g
      case None => throw new IllegalStateException("Replacing one variable by another should not fail")
    }

    override def constructInstanceAndSubst(f: Formula, axiom: Formula): Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(Assign(x:Variable, t), p) =>
        // construct substitution
        val aX = Variable("x", None, Real)
        val aT = Variable("t", None, Real)
        val aP = Function("p", None, Real, Bool)
        val l = List(new SubstitutionPair(aT, t), new SubstitutionPair(ApplyPredicate(aP, x), p))
        // construct axiom instance: [x:=t]p(x) <-> \forall x . (x=t -> p(x))
        val g = Forall(Seq(x), Imply(Equals(Real, x,t), p))
        val axiomInstance = Equiv(f, g)
        val alpha = new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(BoxModality(Assign(_, _), _), Forall(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(alphaRenamingT(x.name, x.index, "x", None)(p.first) & alphaRenamingT(x.name, x.index, "x", None)(p.second))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
        // rename to match axiom if necessary
        val (ax, cont) = if (x.name == "x" && x.index == None) (axiom, None) else (replace(axiom)(aX, x), Some(alpha))
        Some(ax, axiomInstance, new Substitution(l), cont)
      case _ => None
    }

  }

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

  // exhaustive equality rewriting
  // check variable disjointness between left and right side
  def isEquality(s: Sequent, p: Position, checkDisjointness: Boolean = false): Boolean = {
    import Helper.names
    p.isAnte && p.inExpr == HereP && (s.ante(p.getIndex) match {
      case Equals(_, a, b) => if (checkDisjointness) names(a).intersect(names(b)).isEmpty else true
      case ProgramEquals(a, b) => /*if (checkDisjointness) variables(a).intersect(variables(b)).isEmpty else*/ true
      case Equiv(a, b) => /*if (checkDisjointness) variables(a).intersect(variables(b)).isEmpty else*/ true
      case _ => false
    })
  }

  def equalityApplicable(left: Boolean, eqPos: Position, p: Position, s: Sequent): Boolean = {
    import Helper.names
    var applicable = false
    val (blacklist, f) = s.ante(eqPos.getIndex) match {
      case Equals(_, a, b) => val search = if(left) a else b
        (names(a) ++ names(b),
          new ExpressionTraversalFunction {
            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case ProgramEquals(a, b) => val search = if(left) a else b
        (names(a) ++ names(b),
          new ExpressionTraversalFunction {
            override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case Equiv(a, b) => val search = if(left) a else b
        (names(a) ++ names(b),
          new ExpressionTraversalFunction {
            override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case _ => throw new IllegalArgumentException("Equality Rewriting not applicable")
    }
    val trav = TraverseToPosition(p.inExpr, f, blacklist)
    val form = (if (p.isAnte) s.ante else s.succ)(p.getIndex)
    ExpressionTraversal.traverse(trav, form)
    applicable
  }

  def equalityRewriting(eqPos: Position, p: Position): Tactic = new ApplyRule(new EqualityRewriting(eqPos, p)) {
    override def applicable(node: ProofNode): Boolean = {
      val res = isEquality(node.sequent, eqPos, true) && (equalityApplicable(true, eqPos, p, node.sequent) || equalityApplicable(false, eqPos, p, node.sequent))
      res
    }
  }

  def equalityRewritingRight(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Right") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos, true) && equalityApplicable(false, eqPos, p, s)

    override def apply(p: Position): Tactic = equalityRewriting(eqPos, p)
  }

  def equalityRewritingLeft(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Left") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos, true) && equalityApplicable(true, eqPos, p, s)

    override def apply(p: Position): Tactic = equalityRewriting(eqPos, p)
  }

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


      override def preG(p: PosInExpr, e: Game): Either[Option[StopTraversal], Game] = if (test(e)) {
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

  // axiom wrappers
  // TODO: Use findPosInExpr to find a position that matches the left side of the axiom and cut in the resulting instance
  // we start with just using findPos to get a top level position

  abstract class AxiomTactic(name: String, axiomName: String) extends PositionTactic(name) {
    val axiom = Axiom.axioms.get(axiomName)
    def applies(f: Formula): Boolean
    final override def applies(s: Sequent, p: Position): Boolean = axiom.isDefined && applies(getFormula(s, p))

    //@TODO Add contract that applies(f) <=> \result.isDefined
    def constructInstanceAndSubst(f: Formula, a: Formula): Option[(Formula, Formula, Substitution, Option[PositionTactic])] = {
      constructInstanceAndSubst(f) match {
        case Some((instance, subst)) => Some((a, instance, subst, None))
        case None => None
      }
    }

    def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = ???

    //@TODO Add contract that applies()=>\result fine
    override def apply(pos: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        axiom match {
          case Some(ax) =>
            constructInstanceAndSubst(getFormula(node.sequent, pos), ax) match {
              case Some((a, axiomInstance, subst, ptac)) =>
                val eqPos = AntePosition(node.sequent.ante.length)
                val branch1Tactic = axiomInstance match {
                  //@TODO Prefer simpler sequent proof rule for <->left rather than congruence rewriting if the position to use it on is on top-level of sequent
                  case Equiv(_, _) => equalityRewriting(eqPos, pos) & (hideT(eqPos) & hideT(pos))
                  case Imply(_, _) if(pos.isAnte  && pos.inExpr == HereP) => modusPonensT(pos, eqPos)
                  case Imply(_, _) if(!pos.isAnte && pos.inExpr == HereP) => ImplyLeftT(eqPos) & (hideT(pos), AxiomCloseT(eqPos.topLevel, pos))
                  case _ => ???
                }
                // hide in reverse order since hiding changes positions
                val hideAllAnte = for(i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                val hideAllSuccButLast = for(i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                //@TODO Insert contract tactic after hiding all which checks that exactly the intended axiom formula remains and nothing else.
                //@TODO Introduce a reusable tactic that hides all formulas except the ones given as argument and is followed up by a contract ensuring that exactly those formuals remain.
                val cont = ptac match {
                  //@TODO Why is it first succedent position that it's to be applied on?
                  case Some(t) => t(SuccPosition(0))
                  case None => NilT
                }
                val branch2Tactic = ((hideAllAnte ++ hideAllSuccButLast).reduce(seqT)) ~ (uniformSubstT(subst, Map(axiomInstance -> a)) & (cont & axiomT(axiomName) & AxiomCloseT))
                Some(cutT(axiomInstance) & onBranch((cutUseLbl,branch1Tactic), (cutShowLbl, branch2Tactic)))
              case None => None
            }
          case None => None
        }
      }
    }

  }

  def debugT(s: String): Tactic = new Tactic("Debug") {
    override def applicable(node: ProofNode): Boolean = true

    override def apply(tool: Tool, node: ProofNode): Unit = {
      println("===== " + s + " ==== " + node.sequent + " =====")
      continuation(this, Success, Seq(node))
    }
  }

  // [?] test
  def boxTestT: PositionTactic = new AxiomTactic("[?] test", "[?] test") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Test(_), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Test(h), p) =>
        // construct substitution
        val aH = PredicateConstant("H")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aH, h), new SubstitutionPair(aP, p))
        // construct axiom instance: [?H]p <-> (H -> p).
        val g = Imply(h, p)
        val axiomInstance = Equiv(f, g)
        Some(axiomInstance, new Substitution(l))
      case _ => None
    }

  }

  def boxNDetAssign: PositionTactic = new AxiomTactic("[:*] assignment", "[:*] assignment") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(NDetAssign(_), _) => true
      case _ => false
    }

    def replace(f: Formula)(o: Variable, n: Variable): Formula = ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case Forall(v, f) => Right(Forall(v.map((name: NamedSymbol) => if(name == o) n else name ), f))
        case Exists(v, f) => Right(Exists(v.map((name: NamedSymbol) => if(name == o) n else name ), f))
        case _ => Left(None)
      }
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = if (e == o) Right(n) else Left(None)
    }, f) match {
      case Some(g) => g
      case None => throw new IllegalStateException("Replacing one variable by another should not fail")
    }

    override def constructInstanceAndSubst(f: Formula, axiom: Formula): Option[(Formula, Formula, Substitution, Option[PositionTactic])] = f match {
      case BoxModality(NDetAssign(x), p) if(Variable.unapply(x).isDefined) =>
        val v = x.asInstanceOf[Variable]
        // construct substitution
        val aX = Variable("x", None, Real)
        val aP = Function("p", None, Real, Bool)
        val l = List(new SubstitutionPair(ApplyPredicate(aP, x), p))
        // construct axiom instance: [x:=*]p(x) <-> \forall x. p(x).
        val g = Forall(Seq(v), p)
        val axiomInstance = Equiv(f, g)
        val alpha = new PositionTactic("Alpha") {
          override def applies(s: Sequent, p: Position): Boolean = s(p) match {
            case Equiv(BoxModality(NDetAssign(_), _), Forall(_, _)) => true
            case _ => false
          }

          override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
              Some(alphaRenamingT(v.name, v.index, "x", None)(p.first) & alphaRenamingT(v.name, v.index, "x", None)(p.second))

            override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
          }
        }
        // rename to match axiom if necessary
        val (ax, cont) = if(v.name != "x" || v.index != None) (replace(axiom)(aX, v), Some(alpha)) else (axiom, None)
        Some(ax, axiomInstance, new Substitution(l), cont)
      case _ => None
    }
  }

  // [;] compose
  def boxSeqT: PositionTactic = new AxiomTactic("[;] compose", "[;] compose") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Sequence(_, _), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Sequence(a, b), p) =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aB = ProgramConstant("b")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aB, b), new SubstitutionPair(aP, p))
        // construct axiom instance: [ a; b ]p <-> [a][b]p.
        val g = BoxModality(a, BoxModality(b, p))
        val axiomInstance = Equiv(f, g)
        Some(axiomInstance, new Substitution(l))
      case _ => None
    }

  }

  // I induction
  def boxInductionT: PositionTactic = new AxiomTactic("I induction", "I induction") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Loop(_), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Loop(a), p) =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aP, p))
        // construct axiom instance: (p & [a*](p -> [a] p)) -> [a*]p
        val g = And(p, BoxModality(Loop(a), Imply(p, BoxModality(a, p))))
        val axiomInstance = Imply(g, f)
        Some(axiomInstance, new Substitution(l))
      case _ => None
    }

  }

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
      override def applies(s: Sequent, p: Position): Boolean = true // TOOD: really check applicablity

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
          Some(axiomInstance, new Substitution(l), (quantified, aX), (instance, aT))
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
                val hideAllAnte = for (i <- node.sequent.ante.length - 1 to 0 by -1) yield hideT(AntePosition(i))
                // this will hide all the formulas in the current succedent (the only remaining one will be the one we cut in)
                val hideAllSuccButLast = for (i <- node.sequent.succ.length - 1 to 0 by -1) yield hideT(SuccPosition(i))
                def alpha(p: Position, q: Variable) = alphaRenamingT(q.name, q.index, "$" + aX.name, aX.index)(p)
                def repl(f: Formula, v: Variable, atTrans: Boolean = true):Formula = f match {
                  case Imply (a, b) => Imply(decompose(replace (a)(v, Variable ("$" + aX.name, aX.index, aX.sort) )), if(atTrans) replace(b)(aT, instance) else b)
                  case _ => throw new IllegalArgumentException("...")
                }
                val replMap = Map(repl(axiomInstance, quantified, false) -> repl(a, aX))
                val branch2Tactic = (((hideAllAnte ++ hideAllSuccButLast).reduce(seqT)) ~
                  alpha(SuccPosition(0, HereP.first), quantified) ~
                  decomposeQuanT(SuccPosition(0, HereP.first)) ~
                  (uniformSubstT(subst, replMap) & uniformSubstT(new Substitution(Seq(new SubstitutionPair(aT, instance))), Map(repl(a, aX) -> repl(a, aX, false))) &
                    (axiomT(axiomName) & alpha(AntePosition(0, HereP.first), aX) & AxiomCloseT)))
                Some(cutT(axiomInstance) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
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
        Some(axiomInstance, new Substitution(l))
      case _ => None
    }
  }

  // [++] choice
  def boxChoiceT: PositionTactic = new AxiomTactic("[++] choice", "[++] choice") {
    override def applies(f: Formula): Boolean = f match {
      case BoxModality(Choice(_, _), _) => true
      case _ => false
    }

    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Substitution)] = f match {
      case BoxModality(Choice(a, b), p) =>
        // construct substitution
        val aA = ProgramConstant("a")
        val aB = ProgramConstant("b")
        val aP = PredicateConstant("p")
        val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aB, b), new SubstitutionPair(aP, p))
        // construct axiom instance: [ a ++ b ]p <-> [a]p & [b]p.
        val g = And(BoxModality(a, p), BoxModality(b, p))
        val axiomInstance = Equiv(f, g)
        Some(axiomInstance, new Substitution(l))
      case _ => None
    }

  }
  
  /**
   * Tactic that makes a proof step based on the top-level operator
   * except when a decision needs to be made (e.g. for loops, differential equations).
   * This tactics step is thus "indecisive", because it will not reach decisions only make progress.
   * @param beta true to use beta rules (such as AndRight) which split branches.
   * @param simplifyProg false to stop working on modalities. True to take simplifying steps on modalities (except when decisions would be needed).
   * @param equiv true to split equivalences.
   * @TODO Rename. Maybe stepAt?
   */
  def indecisive(beta: Boolean, simplifyProg: Boolean, quantifiers: Boolean, equiv: Boolean = false): PositionTactic = new PositionTactic("Indecisive") {
    override def applies(s: Sequent, p: Position): Boolean = getTactic(s, p).isDefined

    def getTactic(s: Sequent, p: Position): Option[Tactic] = {
      val f = getFormula(s, p)
      val res = f match {
        case Not(_) => if(p.isAnte) Some(NotLeftT(p)) else Some(NotRightT(p))
        case And(_, _) => if(p.isAnte) Some(AndLeftT(p)) else if(beta) Some(AndRightT(p)) else None
        case Or(_, _) => if(p.isAnte) if(beta) Some(OrLeftT(p)) else None else Some(OrRightT(p))
        case Imply(_, _) => if(p.isAnte) if(beta) Some(ImplyLeftT(p)) else None else Some(ImplyRightT(p))
        case Equiv(_, _) => if(equiv) if(p.isAnte) Some(EquivLeftT(p)) else Some(EquivRightT(p)) else None
        case BoxModality(prog, f) if(simplifyProg) => prog match {
          case Sequence(_, _) => Some(boxSeqT(p))
          case Choice(_, _) => Some(boxChoiceT(p))
          case Assign(_, _) => Some(assignment(p))
          // case Assign(_, _) => Some(assignT(p))
          case NDetAssign(_) => Some(boxNDetAssign(p))
          case Test(_) => Some(boxTestT(p))
          case _ => None
        }
        //@TODO case DiamondModality(prog, f)
        case Forall(_, _) if(quantifiers && !p.isAnte) => Some(skolemizeT(p))
        case Exists(_, _) if(quantifiers && p.isAnte) => Some(skolemizeT(p)) //@TODO Make sure skolemizeT works
        case _ => None
      }
      res
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = getTactic(node.sequent, p)
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

}
