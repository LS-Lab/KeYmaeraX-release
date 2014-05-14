package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ApplyRule, ApplyPositionTactic, PositionTactic, Tactic}
import scala.Unit
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import scala.language.postfixOps
import edu.cmu.cs.ls.keymaera.tools.JLinkMathematicaLink

/**
 * In this object we collect wrapper tactics around the basic rules and axioms.
 *
 * Created by Jan-David Quesel on 4/28/14.
 */
object TacticLibrary {

  /**
   * Tactics for real arithmetic
   */
  
  def desequentialization(s : Sequent) = {
    //TODO-nrf Not sure what to do with pref.
    val assumption = 
      if(s.ante.isEmpty) ??? //TODO not sure what to do here.
      else s.ante.reduce( (l,r) => And(l,r) )

    val implicant =
      if(s.succ.isEmpty) ??? //TODO not sure what to do here.
      else s.succ.reduce( (l,r) => Or(l,r) )

    Imply(assumption, implicant)
  }

  //????
  def deskolemize(f : Formula) = {
    val FV = SimpleExprRecursion.getFreeVariables(f)
    Forall(FV, f)
  }
  
  def addRealArithLemma (f : Formula) : (java.io.File, Formula) = {
    //Find the solution
    val solution = new JLinkMathematicaLink().qe(f)
    val result = Equiv(f,solution)
    
    //Save the solution to a file.
    val file = getUniqueLemmaFile()
    KeYmaeraPrettyPrinter.saveProof(file, result)
    
    //Return the file where the result is saved, together with the result.
    (file, result)
  }
  
  private def getUniqueLemmaFile(idx:Int=0):java.io.File = {
    val f = new java.io.File("QE" + idx.toString() + ".alp")
    if(f.exists()) getUniqueLemmaFile(idx+1)
    else f
  }

  /** *******************************************
    * Basic Tactics
    * *******************************************
    */

  def findPosAnte(posT: PositionTactic): Tactic = new ApplyPositionTactic("FindPosAnte (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = findPosition(p.sequent).isDefined

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.ante.length) {
        val pos = new Position(true, i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      return None
    }
  }

  def findPosSucc(posT: PositionTactic): Tactic = new ApplyPositionTactic("FindPosSucc (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = findPosition(p.sequent).isDefined

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.succ.length) {
        val pos = new Position(false, i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      return None
    }
  }

  def AndLeftT: PositionTactic = new PositionTactic("AndLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AndLeftFindT: Tactic = findPosAnte(AndLeftT)

  def AndRightT: PositionTactic = new PositionTactic("AndRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case And(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(AndRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def AndRightFindT: Tactic = findPosSucc(AndRightT)

  def OrLeftT: PositionTactic = new PositionTactic("OrLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrLeftFindT: Tactic = findPosAnte(OrLeftT)

  def OrRightT: PositionTactic = new PositionTactic("OrRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Or(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(OrRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def OrRightFindT: Tactic = findPosSucc(OrRightT)

  def ImplyLeftT: PositionTactic = new PositionTactic("ImplyLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Imply(_, _) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyLeftFindT: Tactic = findPosAnte(ImplyLeftT)

  def ImplyRightT: PositionTactic = new PositionTactic("ImplyRight") {
    def applies(s: Sequent, p: Position) = !p.isAnte && (s.succ(p.index) match {
      case Imply(_, _) => true
      case _ => false
    })

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(ImplyRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def ImplyRightFindT: Tactic = findPosSucc(ImplyRightT)

  def NotLeftT: PositionTactic = new PositionTactic("NotLeft") {
    def applies(s: Sequent, p: Position) = if (p.isAnte) s.ante(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotLeft(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def NotLeftFindT: Tactic = findPosAnte(NotLeftT)

  def NotRightT: PositionTactic = new PositionTactic("NotRight") {
    def applies(s: Sequent, p: Position) = if (!p.isAnte) s.succ(p.index) match {
      case Not(_) => true
      case _ => false
    } else false

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(NotRight(pos)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }
  }

  def NotRightFindT: Tactic = findPosSucc(NotRightT)

  def hideT: PositionTactic = new PositionTactic("Hide") {
    def applies(s: Sequent, p: Position) = true

    def apply(pos: Position): Tactic = new Tactics.ApplyRule(if (pos.isAnte) HideLeft(pos) else HideRight(pos)) {
      override def applicable(node: ProofNode): Boolean = true
    }
  }

  def cutT(g: (ProofNode => Option[Formula])): Tactic = new Tactic("Cut") {
    def applicable(pn: ProofNode): Boolean = g(pn) match {
      case Some(_) => true
      case _ => false
    }

    def apply(tool: Tool, p: ProofNode): Unit = g(p) match {
      case Some(t) => {
        val apTactic = new Tactics.ApplyRule(Cut(t)) {
          override def applicable(node: ProofNode): Boolean = node == p
        };
        apTactic.continuation = continuation
        apTactic.dispatch(this, p)
      }
      case _ => continuation(this, Failed, Seq(p))
    }
  }

  def cutT(f: Formula): Tactic = cutT((x: ProofNode) => Some(f))

  def AxiomCloseT: Tactic = new Tactic("AxiomClose") {
    def apply(tool: Tool, p: ProofNode): Unit = findPositions(p.sequent) match {
      case Some((a, b)) => {
        val t = new Tactics.ApplyRule(AxiomClose(a, b)) {
          override def applicable(node: ProofNode): Boolean = node == p
        }
        t.continuation = continuation
        t.dispatch(this, p)
      }
      case None => continuation(this, Failed, Seq(p))
    }

    def findPositions(s: Sequent): Option[(Position, Position)] = {
      for (f <- s.ante; g <- s.succ)
        if (f == g) return Some((new Position(true, s.ante.indexOf(f)), new Position(false, s.succ.indexOf(g))))
      None
    }

    override def applicable(node: ProofNode): Boolean = findPositions(node.sequent) match {
      case Some(_) => true
      case _ => false
    }
  }

  def axiomT(id: String): Tactic = Axiom.axioms.get(id) match {
    case Some(_) => new Tactics.ApplyRule(Axiom(id)) {
      override def applicable(node: ProofNode): Boolean = true
    }
    case _ => throw new IllegalArgumentException("Unknown axiom " + id)
  }


  def uniformSubstT(subst: Substitution, delta: (Map[Formula, Formula])) = new Tactic("Uniform Substitution") {
    def applicable(pn: ProofNode) = true

    def apply(tool: Tool, p: ProofNode): Unit = {
      val ante = for (f <- p.sequent.ante) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      val succ = for (f <- p.sequent.succ) yield delta.get(f) match {
        case Some(frm) => frm
        case _ => f
      }
      val t = new Tactics.ApplyRule(UniformSubstitution(subst, Sequent(p.sequent.pref, ante, succ))) {
        override def applicable(node: ProofNode): Boolean = node == p
      }
      t.continuation = continuation
      t.dispatch(this, p)
    }

  }

  // assignment tactic (alpha renaming and then assignment rule)
  def assignmentFindAnte = findPosAnte(assignment)
  def assignmentFindSucc = findPosSucc(assignment)
  def assignmentFind = assignmentFindSucc | assignmentFindAnte
  // it would be great if we could access the same position to apply the imply right rule
  // FIXME: this only works for toplevel positions since there the positions are stable
  def assignmentFindImpl = findPosSucc(assignment & ImplyRightT) | findPosAnte(assignment & ImplyLeftT)

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

  val uniquify = new PositionTactic("Uniquify") {
    // for now only on top level
    def getAssignment(s: Sequent, p: Position): Option[(String, Option[Int], Term)] = (if (p.isAnte) s.ante else s.succ)(p.index) match {
        case BoxModality(Assign(Variable(name, i, _), e)) => Some(name, i, e)
        case DiamondModality(Assign(Variable(name, i, _), e)) => Some(name, i, e)
        case a => None
      }
    override def applies(s: Sequent, p: Position): Boolean = (p.inExpr == HereP) && getAssignment(s, p).isDefined


    override def apply(p: Position): Tactic = new Tactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def apply(tool: Tool, node: ProofNode): Unit = {
        val (n, idx) = getAssignment(node.sequent, p) match {
          case Some((a, b, _)) => (a, b)
          case None => throw new IllegalArgumentException("Cannot apply to " + node)
        }
        val vars = Helper.variables(node.sequent).filter((ns: NamedSymbol) => ns.name == n)
        require(vars.size > 0, "The variable we want to rename was not found in the sequent all together " + n + " " + node.sequent)
        // we do not have to rename if there are no name clashes
        if(vars.size > 1) {
          val maxIdx: Option[Int] = (vars.map((ns: NamedSymbol) => ns.index)).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) => acc match {
            case Some(a) => i match {
              case Some(b) => if (a < b) Some(b) else Some(a)
              case None => Some(a)
            }
            case None => i
          })
          val tIdx: Option[Int] = maxIdx match {
            case None => Some(0)
            case Some(a) => Some(a+1)
          }
          // dispatch alpha conversion tactic
          val app = new ApplyRule(new AlphaConversion(p, n, idx, n, tIdx)) {
            override def applicable(n: ProofNode): Boolean = n == node
          }
          app.continuation = continuation
          app.dispatch(this, node)
        }

      }
    }

  }

  // exhaustive equality rewriting
  def isEquality(s: Sequent, p: Position): Boolean = p.isAnte && p.inExpr == HereP && (s.ante(p.getIndex) match {
      case Equals(_, a, b) => true
      case ProgramEquals(a, b) => true
      case Equiv(a, b) => true
      case _ => false
    })

  def equalityApplicable(left: Boolean, eqPos: Position, p: Position, s: Sequent): Boolean = {
    import Helper.variables
    var applicable = false
    val (blacklist, f) = s.ante(eqPos.getIndex) match {
      case Equals(_, a, b) => val search = if(left) a else b; println("Searching for " + search)
        (variables(a) ++ variables(b),
          new ExpressionTraversalFunction {
            override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
              println("found " + e + " with " + e == search)
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case ProgramEquals(a, b) => val search = if(left) a else b
        (variables(a) ++ variables(b),
          new ExpressionTraversalFunction {
            override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
              if (e == search) applicable = true
              Left(Some(new StopTraversal {}))
            }
          })
      case Equiv(a, b) => val search = if(left) a else b
        (variables(a) ++ variables(b),
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
    println("Looking in " + form + " at " + p)
    ExpressionTraversal.traverse(trav, form)
    applicable
  }

  def equalityRewriting(eqPos: Position, p: Position): Tactic = new ApplyRule(new EqualityRewriting(eqPos, p)) {
    override def applicable(node: ProofNode): Boolean = {
      println("IsEquality " + isEquality(node.sequent, eqPos))
      println("Left app " + equalityApplicable(true, eqPos, p, node.sequent))
      println("Right app " + equalityApplicable(false, eqPos, p, node.sequent))
      isEquality(node.sequent, eqPos) && (equalityApplicable(true, eqPos, p, node.sequent) || equalityApplicable(false, eqPos, p, node.sequent))
    }
  }

  def equalityRewritingRight(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Right") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos) && equalityApplicable(false, eqPos, p, s)

    override def apply(p: Position): Tactic = equalityRewriting(eqPos, p)
  }

  def equalityRewritingLeft(eqPos: Position): PositionTactic = new PositionTactic("Equality Rewriting Left") {

    override def applies(s: Sequent, p: Position): Boolean = isEquality(s, eqPos) && equalityApplicable(true, eqPos, p, s)

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
        println("Navigated to " + p + " " + e)
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
          return Some(new Position(true, i, posInExpr))
        }
      }
    }
    for(i <- 0 until s.succ.length) {
      if(ignore == null || ignore.isAnte || ignore.getIndex != i) {
        ExpressionTraversal.traverse(f, s.succ(i))
        if (posInExpr != null) {
          return Some(new Position(false, i, posInExpr))
        }
      }
    }
    None
  }

  def findPosInExpr(left: Boolean, s: Sequent, eqPos: Position): Option[Position] = {
    val eq = s.ante(eqPos.getIndex)
    val blacklist = Helper.variables(eq)
    val search: Expr = eq match {
      case Equals(_, a, b) => if(left) a else b
      case ProgramEquals(a, b) => if(left) a else b
      case Equiv(a, b) => if(left) a else b
      case _ => throw new IllegalArgumentException("Equality Rewriting does not work for " + eq)
    }
    findPosInExpr(s, blacklist, search, eqPos)
  }

  def eqRewritePos(left: Boolean, eqPos: Position): Tactic = new Tactic("Apply Equality Left") {
    require(eqPos.isAnte && eqPos.inExpr == HereP, "Equalities for rewriting have to be in the antecedent")

    override def applicable(node: ProofNode): Boolean = findPosInExpr(left, node.sequent, eqPos).isDefined

    override def apply(tool: Tool, node: ProofNode): Unit = {
      val p = findPosInExpr(left, node.sequent, eqPos) match {
        case Some(pos) => pos
        case None => throw new IllegalArgumentException("Equality rewriting is not applicable to " + node + " with eq at " + eqPos)
      }
      val t = equalityRewriting(eqPos, p)
      val hide = hideT(new Position(p.isAnte, p.getIndex, HereP))
      hide.continuation = continuation
      t.continuation = Tactics.onSuccess(hide)
      t.dispatch(this, node)
    }
  }

  def eqLeft(exhaustive: Boolean): PositionTactic = new PositionTactic("Find Equality and Apply Right to Left") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && isEquality(s, p) && findPosInExpr(true, s, p).isDefined

    override def apply(p: Position): Tactic = if(exhaustive) eqRewritePos(true, p)* else eqRewritePos(true, p)
  }

  val eqLeftFind = findPosAnte(eqLeft(false))

  val eqLeftFindExhaustive = findPosAnte(eqLeft(true))

  def eqRight(exhaustive: Boolean): PositionTactic = new PositionTactic("Find Equality and Apply Left to Right") {
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && isEquality(s, p) && findPosInExpr(false, s, p).isDefined

    override def apply(p: Position): Tactic = if(exhaustive) eqRewritePos(false, p)* else eqRewritePos(false, p)
  }

  val eqRightFind = findPosAnte(eqRight(false))

  val eqRightFindExhaustive = findPosAnte(eqRight(true))

  // axiom wrappers
  // TODO: Use findPosInExpr to find a position that matches the left side of the axiom and cut in the resulting instance
  // we start with just using findPos to get a top level position

  // [?] test
  def boxTestT: PositionTactic = new PositionTactic("[?] test") {
    def getFormula(s: Sequent, p: Position): Formula = {
      require(p.inExpr == HereP)
      if(p.isAnte) s.ante(p.getIndex) else s.succ(p.getIndex)
    }
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case BoxModality(Test(_), _) => true
      case _ => false
    }

    override def apply(pos: Position): Tactic = new Tactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def apply(tool: Tool, node: ProofNode): Unit = {
        getFormula(node.sequent, pos) match {
          case f@BoxModality(Test(h), p) => {
            // construct substitution
            val aH = PredicateConstant("H")
            val aP = PredicateConstant("p")
            val l = List(new SubstitutionPair(aH, h), new SubstitutionPair(aP, p))
            // [?H]p <-> (H -> p).
            val g = Imply(h, p)
            val axiomInstance = Equiv(f, g)
            val axiom = Equiv(BoxModality(Test(aH), aP), Imply(aH, aP))
            val eqPos = new Position(true, node.sequent.ante.length, HereP)
            val branch1Tactic = equalityRewriting(eqPos, pos) & (hideT(eqPos) & hideT(pos))
            // TODO: make sure that this substitution works by renaming if necessary, or by hiding everything else in the sequent
            val branch2Tactic = uniformSubstT(new Substitution(l), Map(axiomInstance -> axiom)) & (axiomT("[?] test") & AxiomCloseT)
            val t = cutT(axiomInstance) & (branch1Tactic, branch2Tactic)
            t.continuation = this.continuation
            t.dispatch(this, node)
          }
          case _ =>
        }
      }
    }
  }

  // [;] compose
   def boxSeqT: PositionTactic = new PositionTactic("[;] compose") {
    def getFormula(s: Sequent, p: Position): Formula = {
      require(p.inExpr == HereP)
      if(p.isAnte) s.ante(p.getIndex) else s.succ(p.getIndex)
    }
    override def applies(s: Sequent, p: Position): Boolean = getFormula(s, p) match {
      case BoxModality(Sequence(_), _) => true
      case _ => false
    }

    override def apply(pos: Position): Tactic = new Tactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def apply(tool: Tool, node: ProofNode): Unit = {
        getFormula(node.sequent, pos) match {
          case f@BoxModality(Sequence(a, b), p) => {
            // construct substitution
            val aA = ProgramConstant("a")
            val aB = ProgramConstant("b")
            val aP = PredicateConstant("p")
            val l = List(new SubstitutionPair(aA, a), new SubstitutionPair(aB, b), new SubstitutionPair(aP, p))
            // [ a; b ]p <-> [a][b]p.
            val g = BoxModality(a, BoxModality(b, p))
            val axiomInstance = Equiv(f, g)
            //val axiom = Equiv(BoxModality(Sequence(aA, aB), aP), BoxModality(aA, BoxModality(aB, aP)))
            val axiom = Axiom.axioms.get("[;] compose") match {
              case Some(a) => a
              case None => { continuation(this, Failed, Seq(node)); return }
            }
            val eqPos = new Position(true, node.sequent.ante.length, HereP)
            val branch1Tactic = equalityRewriting(eqPos, pos) & (hideT(eqPos) & hideT(pos))
            // TODO: make sure that this substitution works by renaming if necessary, or by hiding everything else in the sequent
            val branch2Tactic = uniformSubstT(new Substitution(l), Map(axiomInstance -> axiom)) & (axiomT("[;] compose") & AxiomCloseT)
            val t = cutT(axiomInstance) & (branch1Tactic, branch2Tactic)
            // TODO wrap this in constructTactic method, so that the code above constrcuts the tactic and the continuation stuff is elsewhere
            t.continuation = this.continuation
            t.dispatch(this, node)
          }
          case _ =>
        }
      }
    }
  }
  // [++] choice
  // I induction

  // TODO write tactic that executes "correct" tactic based on top-level operator


}

/**
 * Simple recursion schemes for expressions.
 * @author Nathan Fulton
 */
object SimpleExprRecursion {
  /**
   * A very simple recusion principle for expressions.
   * I couldn't figure out how to do this using the epxression traversal library.
   * @param T the return type.
   * @param e The expression to recurse on
   * @param f A function for processing stopping points in the recursion (nullary expressions and anything specified by partialStop)
   * @param join A function for joining a list of T's returned from binary or ternary expressions.
   * @param partialStop A function specifying where recursion should be cut short.
   */
  def ePartRec[T](e : Expr, f : Expr => T, join : List[T] => T, partialStop : Expr => Boolean) : T = {
    if(partialStop(e)) f(e) //note: we also return f(e) when e in nullary and no recursion is possible.
    else e match {
      case e : Unary   => ePartRec(e.child, f, join, partialStop)
      case e : Binary  => {
        val l = ePartRec(e.left,f,join,partialStop)
        val r = ePartRec(e.right,f,join,partialStop)
        join(List(l,r))
      }
      case e : Ternary => {
        val one = ePartRec(e.fst,f,join,partialStop)
        val two = ePartRec(e.snd,f,join,partialStop)
        val three = ePartRec(e.thd,f,join,partialStop)
        join(List(one,two,three))
      }
      case True()      => f(e)
      case False()     => f(e)
      case e : NamedSymbol => f(e)
      case e : Number.NumberObj => f(e)
      case NFContEvolve(vars: Seq[NamedSymbol], x: Term, theta: Term, formula: Formula) => {
        val varsResult    = vars.map(v => ePartRec(v, f, join, partialStop)).toList
        val xResult       = ePartRec(x,f,join,partialStop)
        val thetaResult   = ePartRec(theta,f,join,partialStop)
        val formulaResult = ePartRec(formula,f,join,partialStop)
        join(varsResult ++ List(xResult, thetaResult, formulaResult))
      }
    }
  }

  /**
   * Example: get free variables using the recursion mechanism.
   */
  def getFreeVariables(e : Expr) : List[NamedSymbol] = {
    type T = List[NamedSymbol]
    
    def f(expr : Expr) : T = expr match {
      case expr : NamedSymbol => List(expr)
      case _ => List()
    }
    
    def join(list : List[T]) = list.reduce(_ ++ _)
    
    //The partialStop function must prevent recursion into binding sites.
    def partialStop(expr : Expr) : Boolean = expr match {
      case expr : Quantifier => true
      case _ => false //TODO-nrf anything else?
    }
    
    ePartRec(e, f, join, partialStop)
  }
}
