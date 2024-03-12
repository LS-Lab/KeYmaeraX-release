/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.Integrator
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.cdgl.Hyp
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import edu.cmu.cs.ls.keymaerax.infrastruct.{
  ExpressionTraversal,
  FormulaTools,
  PosInExpr,
  SubstitutionHelper,
  UnificationMatch,
}
import StandardLibrary._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.tools.ConversionException

/** Checks a Kaisar proof term, after all elaboration/transformation passes have been applied */
object ProofChecker {
  // If true, print more debug info while doing arithmetic proofs

  /** @return query for selector */
  def methodAssumptions(con: Context, sel: Selector, goal: Formula): ContextQuery = (sel match {
    case DefaultSelector =>
      // @TODO: It should be okay for ProgramVars resulting from DefaultSelector to match nothing in InverseGhost case.
      //  or do we want to filter them out here?
      val fv = StaticSemantics(goal).fv
      val candidates = fv.toSet.toList.map((v: Variable) => ProgramVar(Variable(v.name)))
      val mentionedVars = VariableSets(con).allVars.map((v: Variable) => v.name)
      // Keep all variables mentioned in assertions or assignments of context (for example)
      candidates.filter(x => mentionedVars.contains(x.x.name)).map(x => QProgramVar(x.x))
    case DefaultAssignmentSelector =>
      // @TODO: It should be okay for ProgramVars resulting from DefaultSelector to match nothing in InverseGhost case.
      //  or do we want to filter them out here?
      val fv = StaticSemantics(goal).fv
      val candidates = fv.toSet.toList.map((v: Variable) => ProgramVar(Variable(v.name)))
      val mentionedVars = VariableSets(con).allVars.map((v: Variable) => v.name)
      // Keep all variables mentioned in assertions or assignments of context (for example)
      candidates.filter(x => mentionedVars.contains(x.x.name)).map(x => QAssignments(x.x, onlySSA = false))
    case ForwardSelector(pt: ProofVar) => List(QProofVar(pt.x))
    case ForwardSelector(pt: ProgramVar) => List(QProgramVar(pt.x))
    case ForwardSelector(pt: ProgramAssignments) => List(QAssignments(pt.x, pt.onlySSA))
    case ForwardSelector(pt) => List(QProofTerm(pt))
    case PatternSelector(e) => List(QUnify(e))
  }).fold[ContextQuery](QNil())(QUnion(_, _))

  /* @return query for method */
  def methodAssumptions(con: Context, m: Method, goal: Formula): ContextQuery = {
    QElaborate(m.selectors.map(methodAssumptions(con, _, goal)).fold[ContextQuery](QNil())(QUnion(_, _)))
  }

  /** @return unit if [[f]] succeeds, else throw [[ProofCheckException]] */
  private def qeAssert(f: => Boolean, assms: List[Formula], fml: Formula, m: Method, outerStatement: ASTNode): Unit = {
    if (!f) {
      val (interpAssums, interpF) = interpretFunctions(assms.toSet, fml)
      outerStatement match {
        // Give simple error message, no statement given
        case Triv() => throw ProofCheckException(s"Couldn't prove goal ${assms
              .mkString(",")} |- $fml with method $m\nElaborated: ${interpAssums.mkString(",")} |- $interpF")
        case s => throw ProofCheckException(
            s"Couldn't prove goal ${assms.mkString(",")} |- $fml with method $m\nElaborated: ${interpAssums
                .mkString(",")} |- $interpF",
            node = s,
          )
      }
    }
  }

  private def freshVar(vs: Set[Variable]): Variable = {
    var num = 0
    while (vs.contains(Variable("ghostVar", Some(num)))) { num = num + 1 }
    Variable("ghostVar", Some(num))
  }

  // @TODO: Soundness, check bound variables
  // @TODO: Soundness, check constructivity of definitions, hmm...
  private def functionGhost(f: FuncOf, vs: Set[Variable]): (Variable, Formula) = {
    val fresh = freshVar(vs)
    val fml = (f.func.name, f.child) match {
      case ("abs", e) =>
        Or(And(GreaterEqual(e, Number(0)), Equal(fresh, e)), And(LessEqual(e, Number(0)), Equal(fresh, Neg(e))))
      case ("min", Pair(l, r)) => Or(And(GreaterEqual(l, r), Equal(fresh, r)), And(LessEqual(l, r), Equal(fresh, l)))
      case ("max", Pair(l, r)) => Or(And(GreaterEqual(l, r), Equal(fresh, l)), And(LessEqual(l, r), Equal(fresh, r)))
      case (name, args) => throw ProofCheckException("Cannot eliminate function: " + name)
    }
    (fresh, fml)
  }

  private def sequentFml(assms: Set[Formula], f: Formula): Formula = {
    if (assms.isEmpty) f else Imply(assms.reduce(And), f)
  }

  // Note: functions have to get interpreted before prop/auto blasting because resulting goals have Or() in assumptions,
  // aren't constructively QE'able
  private def interpretFunctions(assms: Set[Formula], f: Formula): (Set[Formula], Formula) = {
    val naiveFormula = sequentFml(assms, f)
    var alreadyGhosted: Map[Term, Variable] = Map()
    var ghostEqs: Set[Formula] = Set()
    var substs: Map[Term, Term] = Map()
    var taboo: Set[Variable] = StaticSemantics(naiveFormula).fv.toSet
    // Note: This code would be made cleaner if we had a postorder traversal version of replacesFree
    def allSubsts(f: Term): Option[Term] = {
      f match {
        case fo: FuncOf => substs.get(f) match {
            case Some(res) => Some(res)
            case None =>
              val argSub = SubstitutionHelper.replacesFree(fo.child)(allSubsts)
              val foSub = FuncOf(fo.func, argSub)
              substs.get(foSub)
          }
        case _ => None
      }
    }
    def applySubsts(fml: Formula): Formula = SubstitutionHelper.replacesFree(fml)(t => allSubsts(t))
    val _ = ExpressionTraversal.traverse(
      new ExpressionTraversalFunction() {
        override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          // If function is seen twice, reuse old ghost.
          case fo @ FuncOf(fn: Function, child: Term) if KaisarProof.builtin.contains(fn) =>
            if (alreadyGhosted.contains(fo)) Right(alreadyGhosted(fo))
            else {
              // If this is a new function application, recursively resolve function symbols so we don't accidentally
              // have function symbols in the goal we hand to mathematica.
              val foApp = SubstitutionHelper.replacesFree(fo)(allSubsts) match {
                case fo: FuncOf => fo
                case _ => fo
              }
              val (fresh, eq) = functionGhost(foApp, taboo)
              alreadyGhosted = alreadyGhosted.+(fo -> fresh)
              taboo = taboo.+(fresh)
              ghostEqs = ghostEqs.+(eq)
              // remember both unexpanded and expanded symbol for completeness.
              // @TODO: this duplication is redundant with allSubst checking of expanded function.
              substs = substs.+((fo -> fresh)).+((foApp -> fresh))
              // ProofOptions.branchCount = 2 * ProofOptions.branchCount
              Right(fresh)
            }
          case _ => Left(None)
        }
      },
      naiveFormula,
    )
    val mapped = assms.map(applySubsts)
    val fullAssms = ghostEqs ++ mapped
    val fullF = applySubsts(f)
    (fullAssms, fullF)
  }

  /* Implement rcf (real-closed fields) method */
  private def rcf(assms: Set[Formula], f: Formula): Boolean = {
    try {
      val fullFml = sequentFml(assms, f)
      if (ProofOptions.debugArith) println("Checking formula with QE: " + fullFml)
      val isValid = edu.cmu.cs.ls.keymaerax.cdgl.ProofChecker.qeValid(fullFml)
      if (ProofOptions.debugArith)
        println(s"QE on formula ${if (isValid) "succeeded" else "failed"} on subgoal $assms |- $f")
      isValid
    } catch { case ce: ConversionException => throw ProofCheckException(msg = "Bug in Kaisar QE wrapper", cause = ce) }
  }

  /* implement heuristic "auto" method, which combines propositional and QE reasoning */
  private def auto(assms: Set[Formula], f: Formula): Boolean = { prop(assms, f, rcf) }

  /* trivial hypothesis-rule method */
  private val hyp: (Set[Formula], Formula) => Boolean = ((fs, f) => fs.contains(f))

  /**
   * Apply alpha (invertible) elimination rules to the context wherever possible, then recursively apply other prop
   * rules.
   * @param leaf
   *   is a proof method applied at leaves of search
   * @return
   *   whether fmls |- f proves propositionally
   */
  private def contextAlphas(fmls: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    fmls.find {
      case _: And => true
      case _: Equiv => true
      case False => true
      case _ => false
    } match {
      case Some(False) => true
      case Some(And(l, r)) => prop(fmls.-(And(l, r)).+(l).+(r), f, leaf)
      case Some(Equiv(l, r)) => prop(fmls.-(And(l, r)).+(l).+(r), f, leaf)
      case _ => conclusionBranching(fmls, f, leaf)
    }
  }

  /**
   * Apply branching, but invertible, elimination rules to the conclusion if possible, then recursively apply other prop
   * rules.
   * @param leaf
   *   is a proof method applied at leaves of search
   * @return
   *   whether assms |- f proves propositionally
   */
  private def conclusionBranching(
      assms: Set[Formula],
      f: Formula,
      leaf: (Set[Formula], Formula) => Boolean = hyp,
  ): Boolean = {
    f match {
      case And(l, r) => prop(assms, l, leaf) && prop(assms, r, leaf)
      case Equiv(l, r) => prop(assms.+(l), r) && prop(assms.+(r), l)
      case _ => contextBetas(assms, f, leaf)
    }
  }

  /**
   * Apply beta (non-invertible) elimination rules to the conclusion if possible, then recursively apply other prop
   * rules.
   * @param leaf
   *   is a proof method applied at leaves of search
   * @return
   *   whether assms |- f proves propositionally
   */
  private def conclusionBeta(
      assms: Set[Formula],
      f: Formula,
      leaf: (Set[Formula], Formula) => Boolean = hyp,
  ): Boolean = {
    f match {
      case Or(l, r) => prop(assms, l, leaf) || prop(assms, r, leaf)
      case _ => ProofOptions.branchCount = ProofOptions.branchCount + 1; leaf(assms, f)
    }
  }

  /**
   * Apply beta (non-invertible) elimination rules to the context if possible, then recursively apply other prop rules.
   * @param leaf
   *   is a proof method applied at leaves of search
   * @return
   *   whether assms |- f proves propositionally
   */
  private def contextBetas(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    assms.find {
      case _: Or => true
      case _: Imply => true
      case _ => false
    } match {
      case Some(Or(l, r)) => prop(assms.-(Or(l, r)).+(l), f, leaf) && prop(assms.-(Or(l, r)).+(r), f, leaf)
      case Some(Imply(l, r)) if assms.contains(l) => prop(assms.-(Imply(l, r)).+(r), f)
      case _ => conclusionBeta(assms, f, leaf)
    }
  }

  /**
   * Prop method which attempts propositional proof.
   * @param leaf
   *   is a proof method applied at leaves of search
   * @return
   *   whether assms |- f proves propositionally
   */
  private def prop(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    // Try alpha (invertible) rules on conclusion first
    f match {
      case True => true // True proves trivially
      case Imply(l, r) => prop(assms.+(l), r, leaf)
      case Not(f) => prop(assms.+(f), False)
      case _ if assms.contains(f) => true
      case _ => contextAlphas(assms, f, leaf)
    }
  }

  private def guardDone(con: Context, delta: Term, interpF: Formula): Boolean = {
    con.getFor match {
      case Some(fr: For) =>
        val postCond = Metric.weakNegation(fr.guard.f, delta)
        interpF == postCond
      case _ => false
    }
  }

  /** @return unit if f proves by method [[m]], else throw. */
  private def apply(con: Context, f: Formula, m: Method, outerStatement: ASTNode = Triv()): Unit = {
    val query = methodAssumptions(con, m, f)
    val result = con.findAll(query)
    val assms = result.formulas
    ProofOptions.branchCount = 1
    val (interpAssums, interpF) = interpretFunctions(assms.toSet, f)
    if (ProofOptions.trace) println(s"Proving ${assms.mkString(", ")} |- $f")
    ProofOptions.countBranches(estimated = true)
    m.atom match {
      case Hypothesis() => qeAssert(hyp(interpAssums, interpF), assms, f, m, outerStatement)
      case RCF() => qeAssert(rcf(interpAssums, interpF), assms, f, m, outerStatement)
      // general-purpose auto heuristic
      case Auto() => qeAssert(auto(interpAssums, interpF), assms, f, m, outerStatement)
      // propositional steps
      case Prop() => qeAssert(prop(interpAssums, interpF), assms, f, m, outerStatement)
      // case exhaustiveness
      case Exhaustive() =>
        val branches = FormulaTools.disjuncts(interpF)
        qeAssert(exhaustive(branches), assms, f, m, outerStatement)
      // discharge goal with structured proof
      case GuardDone(Some(delta)) => qeAssert(guardDone(con, delta, interpF), assms, f, m, outerStatement)
      case ByProof(proof: Statements) => apply(con, proof)
    }
    ProofOptions.countBranches()
  }

  /**
   * exhaustive proof method which is used by default to check whether very simple case analyses are constructively
   * exhaustive
   */
  // @TODO: Make more complete
  private def exhaustive(es: List[Expression]): Boolean = {
    val exprs = es.sortWith((l, r) =>
      (l, r) match {
        case (_: Greater, _: Less) => true
        case (_: GreaterEqual, _: Less) => true
        case (_: Greater, _: LessEqual) => true
        case (_: GreaterEqual, _: LessEqual) => true
        case (_: Less, _: Greater) => false
        case (_: Less, _: GreaterEqual) => false
        case (_: LessEqual, _: Greater) => false
        case (_: LessEqual, _: GreaterEqual) => false
        case _ => l.toString < r.toString
      }
    )
    exprs match {
      case (Greater(l1, r1) :: Less(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(l1, r1) :: Less(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (Greater(l1, r1) :: LessEqual(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(l1, r1) :: LessEqual(l2, Plus(r2, Number(k))) :: Nil) => l1 == l2 && r1 == r2 && k > 0

      case (Greater(Plus(l1, Number(k)), r1) :: Less(l2, r2) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(Plus(l1, Number(k)), r1) :: Less(l2, r2) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (Greater(Plus(l1, Number(k)), r1) :: LessEqual(l2, r2) :: Nil) => l1 == l2 && r1 == r2 && k > 0
      case (GreaterEqual(Plus(l1, Number(k)), r1) :: LessEqual(l2, r2) :: Nil) => l1 == l2 && r1 == r2 && k > 0

      case (Greater(l1, r1: Number) :: Less(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
      case (GreaterEqual(l1, r1: Number) :: Less(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
      case (Greater(l1, r1: Number) :: LessEqual(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
      case (GreaterEqual(l1, r1: Number) :: LessEqual(l2, r2: Number) :: Nil) => l1 == l2 && r1.value < r2.value
      case ((fml: Formula) :: True :: _) if isExecutable(fml) => true
      case _ => false
    }
  }

  /** @return unit only if [[LetSym]] statement is admissible (does not violate soundness conditions) */
  private def admitLetFun(con: Context, lf: LetSym): Unit = {
    val LetSym(f, args, body) = lf
    val sigBody = StaticSemantics.signature(body)
    val sig = con.signature.keySet
    // @TODO: better check where we allow line labels but catch other undefined terms. must allow forward def.
    val unboundFunctions = sigBody
      .--(KaisarProof.builtin ++ sig)
      .filter({
        case (fn: Function) => !fn.interpreted && fn.name != "at"
        case _ => true
      })
    if (sig.contains(lf.asFunction)) {
      throw ProofCheckException(s"Multiply-defined function definition ${f.name}", node = lf)
    } else if (unboundFunctions.nonEmpty) {
      throw ProofCheckException(
        s"Definition of function ${f.name} refers to undefined symbols: $unboundFunctions",
        node = lf,
      )
    }
  }

  /** Collect facts and assignments preceding an ODE, which are used to check the ODE proof */
  private case class ODEProofHeader(
      namedFacts: Map[Ident, Formula],
      unnamedFacts: Set[Formula],
      assigns: Map[Variable, Term],
      ghostAssigns: Map[Variable, Term],
      phiAssigns: Map[Variable, Term],
  ) {
    def addFact(x: Option[Ident], fml: Formula): ODEProofHeader = {
      x match {
        case None => ODEProofHeader(namedFacts, unnamedFacts.+(fml), assigns, ghostAssigns, phiAssigns)
        case Some(x) => ODEProofHeader(namedFacts.+(x -> fml), unnamedFacts, assigns, ghostAssigns, phiAssigns)
      }
    }

    def addPhiAssign(x: Ident, f: Term): ODEProofHeader = {
      f match {
        case f: Variable =>
          val renameAssigns = if (assigns.contains(f)) assigns.+(x -> assigns(f)) else assigns
          val renameGhostAssigns = if (ghostAssigns.contains(f)) ghostAssigns.+(x -> ghostAssigns(f)) else ghostAssigns
          ODEProofHeader(namedFacts, unnamedFacts, renameAssigns, renameGhostAssigns, phiAssigns.+(x -> f))
        case f => ODEProofHeader(namedFacts, unnamedFacts, assigns, ghostAssigns, phiAssigns.+(x -> f))
      }
    }

    def addAssign(x: Ident, f: Term): ODEProofHeader =
      ODEProofHeader(namedFacts, unnamedFacts, assigns.+(x -> f), ghostAssigns.+(x -> f), phiAssigns)
    def addGhostAssign(x: Ident, f: Term): ODEProofHeader =
      ODEProofHeader(namedFacts, unnamedFacts, assigns, ghostAssigns.+(x -> f), phiAssigns)
  }

  private object ODEProofHeader {
    val empty: ODEProofHeader = ODEProofHeader(Map(), Set(), Map(), Map(), Map())
  }

  private case class ODEContext(c: Context, header: ODEProofHeader) {
    def bakePhi: ODEContext = ODEContext(c.bakePhi, header)
    def applyPhi(fml: Formula): Formula = SubstitutionHelper.replacesFree(fml)({
      case v: Variable => header.phiAssigns.get(v)
      case _ => None
    })
    def containsFact(fml: Formula, shouldApplyPhi: Boolean = true): Boolean = {
      val fmls = if (shouldApplyPhi) Set(fml, applyPhi(fml)) else Set(fml)
      val set = header.namedFacts.values.toSet ++ header.unnamedFacts
      set.intersect(fmls).nonEmpty
    }
  }
  private object ODEContext {
    def apply(c: Context): ODEContext = {
      val last = c.lastBlockSmall
      val header = last
        .ss
        .foldLeft(ODEProofHeader.empty)({ case (acc, s) =>
          s match {
            case Phi(Modify(ps, (x, Some(f)) :: Nil)) => acc.addFact(ps.headOption, Equal(x, f)).addPhiAssign(x, f)
            case Ghost(Modify(ps, (x, Some(f)) :: Nil)) => acc.addFact(ps.headOption, Equal(x, f)).addGhostAssign(x, f)
            // case Modify(ps, (x, None) :: Nil) => acc.
            //// acc.addAssign()
            // acc.addFact(ps.headOption, Equal(x, f)).addAssign(x, f)
            case Modify(ps, (x, Some(f)) :: Nil) => acc.addFact(ps.headOption, Equal(x, f)).addAssign(x, f)
            case Ghost(Note(x, pt, Some(fml))) => acc.addFact(Some(x), fml)
            case Note(x, pt, Some(f)) => acc.addFact(Some(x), f)
            case Assert(x: Variable, f, m) => acc.addFact(Some(x), f)
            case Assume(x: Variable, f) => acc.addFact(Some(x), f)
            case Assert(Nothing, f, m) => acc.addFact(None, f)
            case Assume(Nothing, f) => acc.addFact(None, f)
            // Even collect ghost facts because ghost proof might need them
            case Ghost(Assert(x: Variable, f, m)) => acc.addFact(Some(x), f)
            case Ghost(Assume(x: Variable, f)) => acc.addFact(Some(x), f)
            case _: PrintGoal => acc
          }
        })
      ODEContext(c, header)
    }
  }

  private def accum(t: Option[DiffStatement], x: DiffStatement): Some[DiffStatement] = t match {
    case None => Some(x)
    case Some(y) => Some(DiffProductStatement(y, x))
  }

  private def accum(t: Option[DomainStatement], x: DomainStatement): Some[DomainStatement] = t match {
    case None => Some(x)
    case Some(y) => Some(DomAnd(y, x))
  }

  /** Is ghost term [[x' = term]] admissible? Allow linear and constant terms. */
  private def admissibleGhost(x: Variable, term: Term): Boolean = {
    if (!StaticSemantics(term).contains(x)) return true
    val (coeff, addend) = term match {
      case (Plus(Times(y: BaseVariable, c), r)) if x == y => (c, r)
      case (Plus(Times(c, y: BaseVariable), r)) if x == y => (c, r)
      case (Plus(r, Times(y: BaseVariable, c))) if x == y => (c, r)
      case (Times(y: BaseVariable, c)) if x == y => (c, Number(0))
      case (Times(c, y: BaseVariable)) if x == y => (c, Number(0))
      case _ => return false
    }
    !StaticSemantics(Pair(coeff, addend)).contains(x)
  }

  // @return elaborated context
  private def applyGhosts(
      kc: ODEContext,
      core: Option[DiffStatement],
      allGhosts: Set[AtomicODEStatement],
  ): Option[DiffStatement] = {
    val ghosts: Option[DiffStatement] = None
    val res = allGhosts.foldLeft[Option[DiffStatement]](ghosts) {
      { case (acc, ds) =>
        ds match {
          case AtomicODEStatement(AtomicODE(DifferentialSymbol(x1), rhs), _) if admissibleGhost(x1, rhs) =>
            if (kc.header.ghostAssigns.contains(x1)) accum(acc, DiffGhostStatement(ds))
            else if (kc.header.assigns.contains(x1)) throw ProofCheckException(
              s"Ghost variable $x1 must be initialized with a ghost assignment, found non-ghost assignment",
              node = ds,
            )
            else throw ProofCheckException(
              s"Ghost variable $x1 needs to be assigned right before differential ghost ${DifferentialSymbol(x1)}",
              node = ds,
            )
          case _: AtomicODEStatement => throw ProofCheckException(s"Inadmissible ghost in $ds", node = ds)
          case _ => throw ProofCheckException(s"Unexpected statement $ds when checking ghosts", node = ds)
        }
      }
    }
    res.map(accum(core, _)).getOrElse(core)
  }

  // @TODO: Should be fine without admissibility check, at least for safety, but maybe not for liveness.
  private def applyInverseGhosts(
      kc: ODEContext,
      core: Option[DiffStatement],
      igs: Set[AtomicODEStatement],
  ): Option[DiffStatement] = {
    val res = igs.foldLeft[Option[DiffStatement]](None) {
      { case (maybeAcc, aode) =>
        (maybeAcc, aode) match {
          case (_, AtomicODEStatement(AtomicODE(DifferentialSymbol(x1), rhs), _)) if admissibleGhost(x1, rhs) =>
            accum(maybeAcc, aode)
          case (Some(_), _: AtomicODEStatement) =>
            throw ProofCheckException(s"Inadmissible ghost in $aode", node = aode)
          case _ =>
            throw ProofCheckException(s"Unexpected statement $aode when checking inverse ODE ghosts", node = aode)
        }
      }
    }
    res.map(accum(core, _)).getOrElse(core)
  }

  private def solveFml(sols: List[(Variable, Term)], f: Formula): Formula = sols
    .foldLeft[Formula](f) { case (acc, (x, f)) => SubstitutionHelper.replaceFree(acc)(x, f) }
  // @TODO: elaborateStable vs elaborateFunctions, why not both
  private def solveAssertion(
      discreteCon: ODEContext,
      odeContext: List[DomainFact],
      proveODE: ProveODE,
      assertion: DomAssert,
      coll: DomCollection,
  ): DomAssert = {
    val DomAssert(x, plainF, m) = assertion
    val f = discreteCon.c.elaborateStable(plainF)
    val methAssumps = m.selectors
    val fullSols = proveODE.proofSolutions.get
    val sols = fullSols.filter({ case ((x, f)) => !proveODE.timeVar.contains(x) })
    val subSol = solveFml(sols, f)
    val subContext = odeContext.map({
      case DomAssume(x, f) => DomAssume(x, solveFml(sols, discreteCon.c.elaborateStable(f)))
      case DomAssert(x, f, m) => DomAssert(x, solveFml(sols, discreteCon.c.elaborateStable(f)), m)
    })
    val baseCon = subContext.foldLeft(discreteCon.c)({
      case (acc, DomAssume(x, f)) => acc.:+(Assume(x, discreteCon.c.elaborateStable(f)))
      case (acc, DomAssert(x, f, m)) => acc.:+(Assert(x, discreteCon.c.elaborateStable(f), m))
    })
    val timeFml = proveODE.duration match {
      case None => GreaterEqual(proveODE.timeVar.get, Number(0))
      case Some((_, dur)) => And(GreaterEqual(proveODE.timeVar.get, Number(0)), GreaterEqual(dur, proveODE.timeVar.get))
    }
    val (id, timeCon) = (baseCon.fresh(), baseCon.ghost(timeFml))
    val solMeth = Using(ForwardSelector(ProofVar(id)) :: methAssumps, RCF())
    apply(timeCon, subSol, solMeth, assertion)
    DomAssert(x, f, m)
  }

  private def inductAssertion(
      odeCon: ODEContext,
      domainFacts: List[DomainFact],
      proveODE: ProveODE,
      assertion: DomAssert,
      coll: DomCollection,
  ): DomAssert = {
    val baseConBC = domainFacts.foldLeft(odeCon.c)({ case (acc, df) =>
      acc.:+(df.mapF(odeCon.c.elaborateStable).asStatement)
    })
    val baseConIH = domainFacts.foldLeft(odeCon.bakePhi.c)({ case (acc, df) =>
      acc.:+(df.mapF(odeCon.c.elaborateStable).asStatement)
    })
    val DomAssert(x, plainF, m) = assertion
    val f = odeCon.c.elaborateStable(plainF)
    val discreteAssumps = coll
      .assumptions
      .toList
      .map({ case DomAssume(x, f) => Assume(x, odeCon.c.elaborateStable(f)) })
    // assignments not needed because they're already handled during lieDerivative
    val ihCon = (discreteAssumps /*++ discreteAssigns*/ ).foldLeft[Context](baseConIH)(_.:+(_))
    val odeMap = proveODE
      .ds
      .allAtoms
      .toList
      .map({ case AtomicODEStatement(AtomicODE(DifferentialSymbol(x), f), _) => (x, f) })
      .toMap
    val lieDerivative = edu.cmu.cs.ls.keymaerax.cdgl.ProofChecker.deriveFormula(f, odeMap)
    val allCutNames = coll.assertions.map(da => da.x.asInstanceOf[Variable])
    val filteredSelectors = m
      .selectors
      .filter({
        case ForwardSelector(ProofVar(x)) if allCutNames.contains(x) => false
        case _ => true
      })
    /* Check base case. Consult context, report error if wrong fact proved in context, attempt automatic proof otherwise.*/
    (odeCon.containsFact(f, shouldApplyPhi = true), x) match {
      case (true, _) =>
      case (false, v: Variable) => odeCon.header.namedFacts.get(v) match {
          case Some(got) => throw ProofCheckException(
              s"You proved ${odeCon.applyPhi(got)} as a base case for differential invariant $x, but needed to prove $f",
              node = assertion,
            )
          case None => apply(baseConBC, f, Using(DefaultAssignmentSelector :: filteredSelectors, Auto()), assertion)
        }
    }
    /* Prove inductive case */
    apply(ihCon, lieDerivative, Using(m.selectors, Auto()), assertion)
    DomAssert(x, f, m)
  }

  private def applyAssertion(
      baseCon: ODEContext,
      odeContext: List[DomainFact],
      proveODE: ProveODE,
      assertion: DomAssert,
      coll: DomCollection,
  ): DomAssert = {
    val DomAssert(x, f, m) = assertion
    m.atom match {
      case Solution() => solveAssertion(baseCon, odeContext, proveODE, assertion, coll)
      case Auto() if proveODE.hasTrueSolution => solveAssertion(baseCon, odeContext, proveODE, assertion, coll)
      case DiffInduction() => inductAssertion(baseCon, odeContext, proveODE, assertion, coll)
      case Auto() if !proveODE.hasTrueSolution => inductAssertion(baseCon, odeContext, proveODE, assertion, coll)
      // should this be handled at an earlier stage?
      case _ => throw ProofCheckException(
          "ODE assertions should only use methods \"induction\" or \"solution\"",
          node = assertion,
        )
    }
  }

  private def applyAssertions(
      kc: ODEContext,
      proveODE: ProveODE,
      assertion: Option[DiffStatement],
      coll: DomCollection,
  ): Option[DomainStatement] = {
    val domAssump = coll.assumptions.toList
    val resAsserts: List[DomainFact] = coll
      .assertions
      .foldLeft[List[DomainFact]](domAssump)({ case ((acc, asrt @ (DomAssert(x, f, m)))) =>
        val DomAssert(xx, ff, mm) = applyAssertion(kc, acc, proveODE, asrt, coll)
        acc.:+(DomAssert(xx, ff, mm))
      })
    val resCon = resAsserts.foldRight[Context](Context.empty)({ case (df, con) => con.:+(df.asStatement) })
    DomainStatement.ofStatement(resCon.s)
  }

  private def applyDuration(
      kc: ODEContext,
      dom: Option[DomainStatement],
      mod: Set[DomModify],
  ): Option[DomainStatement] = {
    if (mod.size >= 2) throw ProofCheckException(
      s"ODE should have at most one duration statement, got: $mod",
      node = mod.toList.tail.head,
    )
    else if (mod.isEmpty) return dom
    if (dom.nonEmpty && !dom.get.isAssertive) throw ProofCheckException(
      s"ODE with duration specification ${mod.toList.head} must prove all domain constraint assumptions, but domain was ${dom.get}",
      node = dom.get,
    )
    val oneMod @ DomModify(id, ap, rhs) = mod.toList.head
    val durFact = GreaterEqual(rhs, Number(0))
    if (!kc.containsFact(durFact)) {
      try { apply(kc.c, durFact, Using(DefaultSelector :: Nil, Auto()), oneMod) }
      catch {
        case t: Throwable => throw ProofCheckException(
            s"ODE has duration $rhs but could not prove $rhs >= 0. To fix this, assert T >= 0 immediately before ODE",
            node = oneMod,
          )
      }
    }
    accum(dom, oneMod)
  }

  private def applyWeakens(
      kc: ODEContext,
      dur: Option[DomainStatement],
      weak: Set[DomainStatement],
  ): Option[DomainStatement] = {
    val weakDom = weak.toList.foldLeft[Option[DomainStatement]](None)(accum)
    weakDom match {
      case None => dur
      case Some(weakStatement) => accum(dur, DomWeak(weakStatement))
    }
  }

  /* Decide what time variable "t" to use for ProveODE in solutions. Often, the time variable is clear from the proof,
   * but if not, consult the context/snapshot to determine a fresh version of the time varable */
  private def initializeTimeVar(context: ODEContext, e: ProveODE): Unit = {
    e.timeVar match {
      case Some(x) =>
      case None =>
        // @TODO: Slow
        val timeVar = Snapshot.ofContext(context.c.:+(e)).increment(ProveODE.defaultTimeVariable)._1
        e.overrideTimeVar(timeVar)
    }
  }

  /** Throw an exception if proveODE unsoundly reuses variables from context. Assumes SSA. */
  private def checkODEContext(kc: ODEContext, proveODE: ProveODE): Unit = {
    val bv = VariableSets(proveODE).boundVars.filter(_.isInstanceOf[BaseVariable])
    val lasts = kc.c.lastBlock.ss.reverse.takeWhile(x => x.isInstanceOf[Phi])
    lasts match {
      case phiBlock =>
        val kvJustPhi = VariableSets(Block(phiBlock)).boundVars
        val clash = bv -- kvJustPhi
        if (clash.nonEmpty) throw ODEAdmissibilityException(clash, node = proveODE)
      case _ => throw ODEAdmissibilityException(bv, node = proveODE)
    }
  }

  /** Check a differential equation proof */
  private def apply(con: Context, inODE: ProveODE): (ProveODE, Formula) = {
    val odeCon = ODEContext(con)
    initializeTimeVar(odeCon, inODE)
    checkODEContext(odeCon, inODE)
    val DiffCollection(cores, ghosts, invGhost) = inODE.ds.doCollect(con)
    val dcCollect @ DomCollection(assume, assert, weak, modify) = inODE.dc.collect
    val core = cores.foldLeft[Option[DiffStatement]](None)(accum)
    val ghosted = applyGhosts(odeCon, core, ghosts)
    val asserted = applyAssertions(odeCon, inODE, ghosted, dcCollect)
    val durated = applyDuration(odeCon, asserted, modify)
    val inversed = applyInverseGhosts(odeCon, ghosted, invGhost)
    val weakened = applyWeakens(odeCon, durated, weak)
    val proveODE = (inversed, weakened) match {
      case (Some(inv), Some(weak)) => ProveODE(inv, weak)
      case _ => throw ProofCheckException("Expected ODE and domain, got none", node = inODE)
    }
    val theMod = modify.toList.headOption
    if (!proveODE.ds.hasDifferentialProgram(proveODE.dc.modifier)) {
      throw ProofCheckException("ODE proof must have at least one non-ghost equation", node = inODE)
    }
    val fml = proveODE.conclusion
    def sameTimeVar(x: Variable, y: Variable): Boolean = {
      (x == y && x.index.isEmpty) || // if not SSA vars
      (x.name == y.name && x.index.contains(0) && y.index.isEmpty) || // if SSA vars 1
      (x.name == y.name && x.index.isDefined && y.index.contains(x.index.get - 1)) // if SSA vars 1
    }
    theMod.foreach({ case DomModify(id, x, f) =>
      val asgn = con.getAssignments(x)
      if (
        !asgn.exists({
          case Equal(y: Variable, Number(n)) if n.toInt == 0 && sameTimeVar(x, y) => true
          case _ => false
        })
      ) throw ProofCheckException(s"Duration variable $x must be initialized to 0 before ODE", node = inODE)
    })
    initializeTimeVar(odeCon, proveODE)
    (proveODE, fml)
  }

  /**
   * Check a proof, or list of statements.
   * @return
   *   final context and conclusion, else raises.
   */
  def apply(con: Context, p: Statements): (Context, Formula) = { apply(con, Block(p)) }

  /**
   * Collect disjuncts only down the right side, rather than *all* disjuncts. This allows us to support case analyses
   * where some branches may be disjunctions
   */
  private def disjoin(fml: Formula, k: Int, node: ASTNode): List[Formula] = {
    (fml, k) match {
      case (_, 1) => fml :: Nil
      case (Or(l, r), _) => l :: disjoin(r, k - 1, node)
      case (_, _) =>
        throw ProofCheckException(s"Not enough branches in case statement, disjunct $fml unmatched", node = node)
    }
  }

  /**
   * @return
   *   unit if the conclusion of selector [[sel]] has the same cases as the [[branches]], i.e. if our case analysis has
   *   exactly the right cases expected by the formula that we case-analyze
   */
  private def compareCasesToScrutinee(con: Context, sel: Selector, branches: List[Expression], node: ASTNode): Unit = {
    // Goal formala "true" should be ignored, case selector should not be "default"
    val query = methodAssumptions(con: Context, sel: Selector, True)
    con.findAll(query).formulas match {
      case fml :: Nil =>
        // TODO: Support cases with non-ground patterns. Improve error messages for case where right-handed split produces too few cases but exhaustive split gives too many
        // Heuristic matching: split disjuncts based on number of cases.
        // If exhaustive split gives the expected number of cases, use that. Else split down the right-hand side
        // until we peel off the right number of cases.
        val disj = FormulaTools.disjuncts(fml)
        if (disj.length == branches.length && disj.toSet != branches.toSet) throw ProofCheckException(
          s"Switch statement branches differ from scrutinee.\nScrutinee: ${disj}\nBranches: $branches",
          node = node,
        )
        else if (disj.length != branches.length) {
          val kDisj = disjoin(fml, branches.length, node)
          if (kDisj.toSet != branches.toSet) throw ProofCheckException(
            s"Switch statement with scrutinee $sel expects branches $kDisj but got $branches",
            node = node,
          )
        }
      case fmls => throw ProofCheckException(
          "Switch expected scrutinee to match exactly one formula, but matches: " + fmls,
          node = node,
        )
    }
  }

  /**
   * @return
   *   (c1, f) where c1 is the elaboration of s (but not con) into a context and f is the conclusion proved by that
   *   elaborated program
   */
  def apply(con: Context, s: Statement): (Context, Formula) = {
    Pragmas.listen(con, s)
    val (Context(resS), resF) = s match {
      case Assert(x, f, m) =>
        val taboo: Set[Variable] = if (con.isGhost) Set() else VariableSets(con).tabooVars
        val elabF = con.elaborateStable(f)
        val debugNames: Set[String] = Set()
        if (debugNames.map(Variable(_): Term).contains(x)) { println("Checking debug assertion: " + x) }
        con.sideEffect(s)
        apply(con, elabF, m, s)
        val conflict = taboo.intersect(StaticSemantics(elabF).fv.toSet)
        if (conflict.nonEmpty)
          throw ProofCheckException(s"Assertion ${f.prettyString} must not mention taboo variables")
        (Context(s), Box(Dual(Test(elabF)), True))
      case Note(x, plainPt, conclusion) =>
        val pt = con.elaborateStable(plainPt)
        val res = ForwardProofChecker(con, pt)
        if (conclusion.isDefined && conclusion.get != res) {
          throw ProofCheckException(s"Note $x expected conclusion ${conclusion.get}, got $res", node = s)
        }
        (Context(Note(x, pt, Some(res))), res)
      case Block(ss) =>
        val (c, fs) = ss.foldLeft[(Context, List[Formula])](Context.empty, List()) { case ((acc, accF), s) =>
          val (cc, ff) = apply(con.:+(acc.s), s)
          (acc.:+(cc.s), accF.:+(ff))
        }
        val ff = fs.reduceRight(concatBox)
        (c, ff)
      case bc @ BoxChoice(left: Statement, right: Statement) =>
        val (conL, conR) = (con.:+(BoxChoiceProgress(bc, 0, Triv())), con.:+(BoxChoiceProgress(bc, 1, Triv())))
        val ((sl, fl), (sr, fr)) = (apply(conL, left), apply(conR, right))
        val (Box(a, p1), Box(b, p2)) = (asBox(fl), asBox(fr))
        val p = unifyFml(p1, p2).getOrElse(throw ProofCheckException("Could not unify branches of choice", node = bc))
        val ss = BoxChoice(sl.s, sr.s)
        (Context(ss), Box(Choice(a, b), p))
      case switch @ Switch(sel, branches: List[(Expression, Expression, Statement)]) =>
        // @TODO: proper expression patterns not just formulas
        val (patterns, plainConds, bodies) = unzip3(branches)
        val conds = plainConds.map(f => con.elaborateStable(f))
        sel match {
          case None =>
            if (!exhaustive(conds)) throw ProofCheckException("Inexhaustive match in switch statement", node = switch)
          case Some(sel) => compareCasesToScrutinee(con, sel, conds, switch)
        }
        val (cons, fmls) = branches
          .zipWithIndex
          .map({
            case (cb, i) => {
              val (c, f) = apply(con.:+(SwitchProgress(switch, i, Triv())), cb._3)
              (c, concatBox(Box(Test(cb._2.asInstanceOf[Formula]), True), f))
            }
          })
          .unzip
        val (as, ps) = fmls.map(asBox).map { case Box(a, p) => (Dual(a), p) }.unzip
        val p = unifyFmls(ps).getOrElse(throw ProofCheckException("Switch branches failed to unify", node = switch))
        (Context(Switch(sel, zip3(patterns, conds, cons.map(_.s), switch))), Box(Dual(as.reduceRight(Choice)), p))
      case While(x, j, s) =>
        val jElab = con.elaborateFunctions(j, Triv())
        val prog = WhileProgress(While(x, jElab, s), Triv())
        val kc = con.:+(prog)
        val (Context(sa), fa) = apply(kc, s)
        val ss = While(x, jElab, sa)
        val Diamond(a, p) = asDiamond(fa)
        val fml = Diamond(Loop(a), p)
        (Context(ss), fml)
      case fr @ For(metX, plainMet0, plainMetIncr, plainMaybeConv, plainGuard, body, guardEpsilon) =>
        // @TODO: Double check side conditions / edge cases
        // throws exception if metric ill-formed
        val taboos = VariableSets(body).boundVars
        // check index variable side condition
        if (taboos.contains(metX)) {
          throw ProofCheckException(s"For loop index variable $metX must not be bound in loop body", node = fr)
        }
        // elaborate loop conditions
        val maybeConv = plainMaybeConv.map(cnv => Assert(cnv.pat, con.elaborateStable(cnv.f), cnv.m))
        val guard = Assume(plainGuard.pat, con.elaborateStable(plainGuard.f))
        val metIncr = con.elaborateStable(plainMetIncr)
        val met0 = con.elaborateStable(plainMet0)
        // check whether loop metric is well-founded, throw if not
        val metric = Metric(metX, metIncr, guard.f, taboos)
        // check additional metric side condition if any, e.g. increment amount must have lower bound
        metric.sideCondition match {
          case None => ()
          case Some(goal) =>
            try { apply(con, goal, Using(List(DefaultSelector), Auto())) }
            catch {
              case pce: ProofCheckException => throw ProofCheckException(
                  "Could not automatically prove that for loop terminates. " +
                    "Double-check the termination condition and ensure that the loop index provably progresses at each step",
                  cause = pce,
                  node = fr,
                )
            }
        }
        // Context used for base cases
        val baseCon = con.:+(Modify(Nil, List((metX, Some(met0)))))
        // test convergence predicate base case
        try { maybeConv.map(cnv => apply(baseCon, cnv)) }
        catch {
          case pce: ProofCheckException => throw ProofCheckException(
              "Could not prove that convergence predicate of for loop holds initially",
              cause = pce,
              node = fr,
            )
        }
        // @TODO: [low priority] consider tracking unelaborated IH in For loop data structure
        val progFor = For(metX, met0, metIncr, maybeConv, guard, body)
        val progCon = ForProgress(progFor, Triv())
        // Check body
        val (sBody, fBody) = apply(con.:+(progCon), body)
        val maybeStepConv = maybeConv.map(cnv =>
          SubstitutionHelper.replacesFree(cnv.f)({
            case bv: BaseVariable if bv == metX => Some(metIncr)
            case _ => None
          })
        )
        val indStepResults = sBody.lastFacts
        val indStepConv = indStepResults.find({ case (kName, kFml, kElab) => maybeStepConv.contains(kElab) })
        // Check that convergence inductive step has been proven which matches the convergence condition, if there is any
        val cnvConcl: Formula = (indStepConv, maybeConv) match {
          case (None, Some(Assert(cnvX, cnvElab, cnvM))) =>
            throw ProofCheckException(s"For loop has no inductive step for convergence predicate $cnvX:$cnvElab")
          case (Some((istepX, istepF, istepElab)), Some(Assert(cnvX, cnvElab, cnvM))) => istepElab
          case _ => True
        }
        // NB: progress is ensured by side conditions / increment conditions, no separate proof needed in loop body */
        // Package proof results
        val Box(a, p) = asBox(fBody)
        val termCond = fr.guardDelta.map(gd => Metric.weakNegation(fr.guard.f, gd))
        val theConcl = (cnvConcl, termCond) match {
          case (True, Some(tc)) => tc
          case (f, None) => f
          case (f, Some(tc)) => And(f, tc)
        }
        // @TODO: reconsider result formula format. Complicated one here needed when proved formula mentions metX though
        val ff = Box(
          Compose(
            Compose(Assign(metX, met0), Dual(Loop(Compose(Dual(a), Assign(metX, metIncr))))),
            Dual(Test(theConcl)),
          ),
          True,
        )
        val ss = For(metX, met0, metIncr, maybeConv, guard, sBody.s, guardEpsilon)
        (Context(ss), ff)
      case bl @ BoxLoop(s: Statement, _) => con.lastFact match {
          case None => throw ProofCheckException(s"No invariant found in $con", node = bl)
          // lastfact,
          case Some((kName, kFml, kElab)) =>
            val progCon = BoxLoopProgress(BoxLoop(s, Some((kName, kFml, Some(kElab)))), Triv())
            val (ss, f) = apply(con.:+(progCon), s)
            val Box(a, p) = asBox(f)
            val res = BoxLoop(ss.s, Some((kName, kFml, Some(kElab))))
            val ff = Box(Loop(a), p)
            val lookup = ss.lastFact
            lookup match {
              case None => throw ProofCheckException(s"Inductive step does not prove invariant", node = bl)
              case Some((kName2, kFml2, kElab2)) if kElab != kElab2 =>
                throw ProofCheckException(
                  s"Inductive step $kElab2 and invariant $kElab differ (after expanding to $kFml2 and $kFml)",
                  node = bl,
                )
              case Some(kFml2) => (Context(res), ff)
            }
        }
      case pode: ProveODE =>
        val (x, y) = apply(con, pode)
        (Context(x), y)

      // @TODO: LetFun and Match should be checked in earlier passes?
      case lf: LetSym => admitLetFun(con, lf); (Context(lf), True)
      case mtch @ Match(pat, e) =>
        try {
          UnificationMatch(pat, e);
          (Context(Match(pat, e)), True)
        } catch {
          case e: ProverException => throw ProofCheckException(s"Pattern match $pat = $e fails to unify", node = mtch)
        }
      case ghost @ Ghost(s) =>
        if (con.isInverseGhost) { throw ProofCheckException("Forward ghost not allowed inside inverse ghost") }
        val (ss, f) = apply(con.withGhost, s)
        val taboo = VariableSets(ss).boundVars
        val fv = StaticSemantics(f).fv
        if (taboo.intersect(fv.toSet).nonEmpty) {
          throw ProofCheckException(s"Ghost variable assignment escapes scope in ghost statement $f", node = ghost)
        }
        (Context(Ghost(ss.s)), True)
      case InverseGhost(s: Statement) =>
        if (con.isGhost) { throw ProofCheckException("Inverse ghost not allowed inside forward ghost") }
        val (ss, f) = apply(con.withInverseGhost, s)
        (Context(InverseGhost(ss.s)), f)
      case PrintGoal(msg) => println(s"[DEBUG] $msg: \n$con\n"); (Context.empty, True)
      case Was(now, was) =>
        val (ss, f) = apply(con, now)
        (Context(Was(ss.s, was)), f)
      case Phi(s) =>
        val (ss, f) = apply(con, s)
        (Context(Phi(ss.s)), f)
      // Proofs that succeed unconditionally
      case mod @ Modify(_, (x, rhs) :: Nil) =>
        val n = x.name
        val xIdx = x.index.getOrElse(-1)
        val freshVar = con.fresh(n)
        val yIdx = freshVar.index.getOrElse(-1)
        if (yIdx > xIdx) {
          throw ProofCheckException(s"Assignment to $x was not in static-single-assignment form", node = mod)
        }
        rhs match {
          case Some(f) =>
            if (StaticSemantics(f).contains(x)) {
              throw ProofCheckException(s"Assignment to $x was not admissible", node = mod)
            }
            (Context(s), Box(Assign(x, f), True))
          case None => (Context(s), Box(AssignAny(x), True))
        }
      case Assume(pat, f) =>
        val elabF = con.elaborateStable(f)
        (Context(s), Box(Test(elabF), True))
      case _: Triv | _: Label => (Context(s), True)
      case pr: Pragma => Pragmas.update(pr.ps); (Context(s), True)
    }
    (Context(ASTNode.locate(resS, s)), resF)
  }
}
