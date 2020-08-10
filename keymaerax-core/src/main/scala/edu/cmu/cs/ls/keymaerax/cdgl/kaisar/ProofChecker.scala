/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.Integrator
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.cdgl.Hyp
import edu.cmu.cs.ls.keymaerax.core.{Variable, _}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, ODEAdmissibilityException, Statements}
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, SubstitutionHelper, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

/** Checks a Kaisar proof term, after all elaboration/transformation passes have been applied */
object ProofChecker {
  // If [[SSA]] is on, apply strict soundness/admissibility checking, which only works if our inputs have been pre-processed
  // with static single assignment. If [[SSA]] is off, do not use strict soundness checking, in which case the checker is not sound.
  val SSA: Boolean = true

  /** @return all formulas selected by a selector */
  private def methodAssumptions(con: Context, m: Selector, goal: Formula): List[Formula] = {
    m match {
      case DefaultSelector =>
        val fv = StaticSemantics(goal).fv
        val res = fv.toSet.toList.flatMap((v: Variable) => con.get(v, wantProgramVar = true).toList)
        res
      case ForwardSelector(pt) => List(ForwardProofChecker(con, pt))
      case PatternSelector(e) => con.unify(e).toList.map(_._2)
    }
  }

  /** @return formulas selected in method, paired with underlying basic method */
  def methodAssumptions(con: Context, m: Method, goal: Formula): (List[Formula], Method) = {
    m match {
      case Using(sels, m) =>
        val assms = sels.flatMap(methodAssumptions(con, _, goal))
        val (assm, meth) = methodAssumptions(con, m, goal)
        (assms ++ assm, meth)
      case RCF() | Auto() | Prop() | Solution() | DiffInduction() | _: ByProof | _: Exhaustive => (List(), m)
    }
  }

  /** @return unit if [[f]] succeeds, else throw [[ProofCheckException]] */
  private def qeAssert(f: => Boolean, assms: List[Formula], fml: Formula, m: Method): Unit = {
    if(!f)
      throw new ProofCheckException(s"Couldn't prove goal ${assms.mkString(",")} |- $fml with method $m")
  }

  /* Implement rcf (real-closed fields) method */
  private def rcf(assms: Set[Formula], f: Formula): Boolean = {
    edu.cmu.cs.ls.keymaerax.cdgl.ProofChecker.qeValid(Imply(assms.foldLeft[Formula](True)(And), f))
  }

  /* implement heuristic "auto" method, which combines propositional and QE reasoning */
  private def auto(assms: Set[Formula], f: Formula): Boolean = {
    prop(assms, f, rcf)
  }

  /* trivial hypothesis-rule method */
  private val hyp: (Set[Formula], Formula) => Boolean = ((fs, f) => fs.contains(f))

  /** Apply alpha (invertible) elimination rules to the context wherever possible, then recursively apply other prop rules.
   * @param leaf is a proof method applied at leaves of search
   * @return whether fmls |- f proves propositionally */
  private def contextAlphas(fmls: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    fmls.find{case _: And => true case _: Equiv => true  case False => true case _ => false} match {
      case Some(False) => true
      case Some(And(l, r)) => prop(fmls.-(And(l,r)).+(l).+(r), f, leaf)
      case Some(Equiv(l, r)) => prop(fmls.-(And(l,r)).+(l).+(r), f, leaf)
      case _ => conclusionBeta(fmls, f, leaf)
    }
  }

  /** Apply beta (non-invertible) elimination rules to the conclusion if possible, then recursively apply other prop rules.
    * @param leaf is a proof method applied at leaves of search
    * @return whether assms |- f proves propositionally */
  private def conclusionBeta(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    f match {
      case And(l, r) => prop(assms, l, leaf) && prop(assms, r, leaf)
      case Equiv(l, r) => prop(assms.+(l), r) && prop(assms.+(r), l)
      case _ => contextBetas(assms, f, leaf)
    }
  }

  /** Apply beta (non-invertible) elimination rules to the context if possible, then recursively apply other prop rules.
    * @param leaf is a proof method applied at leaves of search
    * @return whether assms |- f proves propositionally */
  private def contextBetas(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    assms.find { case _: Or => true case _: Imply => true case _ => false } match {
      case Some(Or(l, r)) => prop(assms.-(Or(l,r)).+(l), f, leaf) || prop(assms.-(Or(l,r)).+(r), f, leaf)
      case Some(Imply(l, r)) => prop(assms.-(Imply(l,r)), l) && prop(assms.-(Imply(l,r)).+(r), f)
      case _ => leaf(assms, f)
    }
  }

  /** Prop method which attempts propositional proof.
    * @param leaf is a proof method applied at leaves of search
    * @return whether assms |- f proves propositionally */
  private def prop(assms: Set[Formula], f: Formula, leaf: (Set[Formula], Formula) => Boolean = hyp): Boolean = {
    // Try alpha (invertible) rules on conclusion first
    f match {
      case True => true  // True proves trivially
      case Imply(l, r) => prop(assms.+(l), r, leaf)
      case Not(f) => prop(assms.+(f), False)
      case _ => contextAlphas(assms, f, leaf)
    }
  }

  /** @return unit if f proves by method [[m]], else throw. */
  private def apply(con: Context, f: Formula, m: Method): Unit = {
    val (assms, meth) = methodAssumptions(con, m, f)
    meth match {
      case RCF() => qeAssert(rcf(assms.toSet, f), assms, f, m)
      // general-purpose auto heuristic
      case Auto() => qeAssert(auto(assms.toSet, f), assms, f, m)
      // propositional steps
      case Prop() => qeAssert(prop(assms.toSet, f), assms, f, m)
      // case exhaustiveness
      case Exhaustive() =>
        val branches = disjoin(f, 0)
        qeAssert (exhaustive(branches), assms, f, m)
      // discharge goal with structured proof
      case ByProof(proof: Statements) => apply(con, proof)
    }
  }

  /** exhaustive proof method which is used by default to check whether very simple case analyses are constructively exhaustive */
  // @TODO: Make more complete
  private def exhaustive(es: List[Expression]): Boolean = {
    val exprs = es.sortWith((l,r) => (l, r) match {
      case (_: Greater, _: Less) => true case (_: GreaterEqual, _: Less) => true
      case (_: Greater, _: LessEqual) => true case (_: GreaterEqual, _: LessEqual) => true
      case (_: Less, _: Greater) => false case (_: Less, _: GreaterEqual) => false
      case (_: LessEqual, _: Greater) => false case (_: LessEqual, _: GreaterEqual) => false
      case _ => l.toString < r.toString
    })
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
      case _ => false
    }
  }

  /**  @return unit only if [[LetFun]] statement is admissible (does not violate soundness conditions) */
  private def admitLetFun(con: Context, lf: LetFun): Unit = {
    val LetFun(f, args, body) = lf
    val sigBody = StaticSemantics.signature(body)
    val sig = con.signature
    val unboundFunctions = sigBody.--(KaisarProof.builtin ++ sig)
    if (sig.contains(lf.asFunction)) {
      throw ProofCheckException(s"Multiply-defined function definition ${f.name}")
    } else if (unboundFunctions.nonEmpty) {
      throw ProofCheckException(s"Definition of function ${f.name} refers to undefined symbols: $unboundFunctions")
    }
  }

  private def accum(t: Option[DiffStatement], x: DiffStatement): Some[DiffStatement] =
    t match {case None => Some(x) case Some(y) => Some(DiffProductStatement(y, x))}

  private def accum(t: Option[DomainStatement], x: DomainStatement): Some[DomainStatement] =
    t match {case None => Some(x) case Some(y) => Some(DomAnd(y, x))}

  /** Is ghost term [[x' = term]] admissible? Allow linear and constant terms. */
  private def admissibleGhost(x: Variable, term: Term): Boolean = {
    if (!StaticSemantics(term).contains(x)) return true
    term match {
      case (Plus(Times(y: BaseVariable, c), r)) => x == y && !StaticSemantics(Pair(c, r)).contains(x)
      case _ => false
    }
  }

  // @return elaborated context
  private def applyGhosts(kc: Context, core: Option[DiffStatement], ds: Set[AtomicODEStatement]): Option[DiffStatement] = {
    val ghosts: Option[DiffStatement] = None
    val res = ds.foldLeft[Option[DiffStatement]](ghosts){{case (acc, ds) =>
    ds match {
      case AtomicODEStatement(AtomicODE(DifferentialSymbol(x1), rhs)) if admissibleGhost(x1, rhs) =>
        accum(acc, DiffGhostStatement(ds))
      case _: AtomicODEStatement => throw ProofCheckException(s"Inadmissible ghost in $ds")
      case _ => throw ProofCheckException(s"Unexpected statement $ds when checking ghosts")
    }}}
    res.map(accum(core, _)).getOrElse(core)
  }

  // @TODO: Should be fine without admissibility check, at least for safety, but maybe not for liveness.
  private def applyInverseGhosts(kc: Context, core: Option[DiffStatement], ds: Set[AtomicODEStatement]): Option[DiffStatement] = {
    val iGhosts: Option[DiffStatement] = None
    val res = ds.foldLeft[Option[DiffStatement]](iGhosts){{case (acc, ds) =>
      ds match {
        case AtomicODEStatement(AtomicODE(DifferentialSymbol(x1), rhs)) if admissibleGhost(x1, rhs) =>
          accum(core, ds)
        case _: AtomicODEStatement => throw ProofCheckException(s"Inadmissible ghost in $ds")
        case _ => throw ProofCheckException(s"Unexpected statement $ds when checking ghosts")
      }}}
    res.map(accum(core, _)).getOrElse(core)
  }

  private def solveFml(sols: List[(Variable, Term)], f: Formula): Formula = sols.foldLeft[Formula](f){case (acc, (x, f)) => SubstitutionHelper.replaceFree(acc)(x,f)}
  private def solveAssertion(discreteCon: Context, odeContext: List[DomainFact], proveODE: ProveODE, assertion: DomAssert, coll: DomCollection): DomAssert = {
    val DomAssert(x, f, m) = assertion
    val methAssumps = m.selectors
    val sols = proveODE.solutions.get
    val subSol = solveFml(sols, f)
    val subContext = odeContext.map({case DomAssume(x ,f) => DomAssume(x, solveFml(sols, f)) case DomAssert(x, f, m) => DomAssert(x, solveFml(sols, f), m)})
    val baseCon = subContext.foldLeft(discreteCon)({case (acc, DomAssume(x, f)) => acc.:+(Assume(x, f)) case (acc, DomAssert(x, f, m)) => acc.:+(Assert(x, f, m))})
    val (id, timeCon) = (baseCon.fresh(), baseCon.ghost(GreaterEqual(proveODE.timeVar.get, Number(0))))
    val solMeth = Using(ForwardSelector(ProofVar(id)) :: methAssumps, RCF())
    apply(timeCon, subSol, solMeth)
    assertion
  }

  private def inductAssertion(discreteCon: Context, odeContext: List[DomainFact], proveODE: ProveODE, assertion: DomAssert, coll: DomCollection): DomAssert = {
    val baseCon = odeContext.foldLeft(discreteCon)({case (acc, DomAssume(x, f)) => acc.:+(Assume(x, f)) case (acc, DomAssert(x, f, m)) => acc.:+(Assert(x, f, m))})
    val DomAssert(x, f, m) = assertion
    val discreteAssumps = coll.assumptions.toList.map({case DomAssume(x, f) => Assume(x, f)})
    val dSet = proveODE.ds.atoms
    val discreteAssigns = dSet.toList.map({case AtomicODEStatement(AtomicODE(dx, e)) => Modify(VarPat(dx, None), Left(e))})
    // @TODO unsound: need to forget baseCon, or rather check that baseCon has been correctly SSA renamed.
    val ihCon = (discreteAssumps ++ discreteAssigns).foldLeft[Context](baseCon)(_.:+(_))
    val odeMap = DifferentialHelper.atomicOdes(proveODE.asODESystem).map({case AtomicODE(DifferentialSymbol(x), f) => (x, f)}).toMap
    val lieDerivative = edu.cmu.cs.ls.keymaerax.cdgl.ProofChecker.deriveFormula(f, odeMap)
    // @TODO: if assertion name is found in context, or is lastFact then look up. May require generalizing lastFact to lastFacts that returns all facts since last state change.
    val allCutNames = coll.assertions.map(da => da.x.asInstanceOf[Variable])
    val filteredSelectors = m.selectors.filter({case ForwardSelector(ProofVar(x)) if allCutNames.contains(x) => false case _ => true})
    apply(baseCon, f, Using(DefaultSelector :: filteredSelectors,  Auto()))
    apply(ihCon, lieDerivative, Using(m.selectors, Auto()))
    assertion
  }

  // val DomAssert(xx, ff, mm) = applyAssertion(kc, assumps, asrt, proveODE, odeSystem, sols)
  private def applyAssertion(baseCon: Context, odeContext: List[DomainFact], proveODE: ProveODE, assertion: DomAssert, coll: DomCollection): DomAssert = {
    val DomAssert(x, f, m) = assertion
    m.atom match {
      case Solution() => solveAssertion(baseCon, odeContext, proveODE, assertion, coll)
      case DiffInduction() => inductAssertion(baseCon, odeContext, proveODE, assertion, coll)
      case _ => throw ProofCheckException("ODE assertions should use methods \"induction\" or \"solve\"")
    }
  }

  /** @TODO: Debug assertion checker. */
  private def applyAssertions(kc: Context, proveODE: ProveODE, assertion: Option[DiffStatement], coll: DomCollection): Option[DomainStatement] = {
    def unpack(ds: Statement): Option[DomainStatement] = ds match {
      case _: Triv => None
      case Block(ss) =>
        val dss = ss.map(unpack).filter(_.isDefined).map(_.get)
        if (dss.isEmpty) None
        else Some(dss.reduceRight(DomAnd))
      case Assume(x, f) => Some(DomAssume(x, f))
      case Assert(x, f, m) => Some(DomAssert(x, f, m))
    }
    val domAssump = coll.assumptions.toList
    val resAsserts: List[DomainFact] =
      coll.assertions.foldLeft[List[DomainFact]](domAssump)({case ((acc, asrt@(DomAssert(x, f, m)))) =>
        val DomAssert(xx, ff, mm) = applyAssertion(kc, acc, proveODE, asrt, coll)
        acc.:+(DomAssert(xx, ff, mm))
      })
    // @TODO: refactor this into common method / refeactor DomAssert vs Assert conversions
    val resCon = resAsserts.foldRight[Context](Context.empty)({
      case (DomAssume(x, f), acc) => acc.:+(Assume(x, f))
      case (DomAssert(x, f, m), acc) => acc.:+(Assert(x, f, m))
    })
    unpack(resCon.s)
  }


  private def applyDuration(kc: Context, dom: Option[DomainStatement], mod: Set[DomModify]): Option[DomainStatement] = {
    if (mod.size >= 2)
      throw ProofCheckException(s"ODE should have at most one duration statement, got: $mod")
    else if (mod.isEmpty) return dom
    if(dom.nonEmpty && !dom.get.isAssertive)
      throw ProofCheckException(s"ODE with duration specification ${mod.toList.head} must prove all domain constraint assumptions, but domain was ${dom.get}")
    val oneMod@DomModify(ap, rhs) = mod.toList.head
    accum(dom, oneMod)
  }

  private def applyWeakens(kc: Context, dur: Option[DomainStatement], weak: Set[DomainStatement]): Option[DomainStatement] = {
    val weakDom = weak.toList.foldLeft[Option[DomainStatement]](None)(accum)
    weakDom match {case None => dur case Some(weakStatement) => accum(dur, DomWeak(weakStatement))}
  }

  /* Decide what time variable "t" to use for ProveODE in solutions. Often, the time variable is clear from the proof,
   * but if not, consult the context/snapshot to determine a fresh version of the time varable */
  private def initializeTimeVar(context: Context, e: ProveODE): Unit = {
    e.timeVar match {
      case Some(x) =>
      case None =>
        // @TODO: Slow
        val timeVar = Snapshot.ofContext(context.:+(e)).increment(ProveODE.defaultTimeVariable)._1
        e.overrideTimeVar(timeVar)
    }
  }

  private def checkODEContext(kc: Context, proveODE: ProveODE): Unit = {
    val bv = VariableSets(proveODE).boundVars.filter(_.isInstanceOf[BaseVariable])
    val kv = VariableSets(kc.s)
    val taboo = kv.freeVars ++ kv.boundVars
    val clash = bv.intersect(taboo)
    if (clash.nonEmpty)
      throw ODEAdmissibilityException(clash)
  }

    /**  Check a differential equation proof */
  // @TODO debug and soundify
  private def apply(con: Context, inODE: ProveODE): (ProveODE, Formula) = {
    initializeTimeVar(con, inODE)
    checkODEContext(con, inODE)
    val DiffCollection(cores, ghosts, invGhost) = inODE.ds.collect
    val dcCollect@DomCollection(assume, assert, weak, modify) = inODE.dc.collect
    val core = cores.foldLeft[Option[DiffStatement]](None)(accum)
    val ghosted = applyGhosts(con, core, ghosts)
    val asserted = applyAssertions(con, inODE, ghosted, dcCollect)
    val durated = applyDuration(con, asserted, modify)
    val inversed = applyInverseGhosts(con, ghosted, invGhost)
    val weakened = applyWeakens(con, durated, weak)
    val proveODE =
      (inversed, weakened) match {
        case (Some(inv), Some(weak)) => ProveODE(inv, weak)
        case _ => throw ProofCheckException("Expected ODE and domain, got none")
      }
    val theMod = modify.toList.headOption
    if (!proveODE.ds.hasDifferentialProgram(proveODE.dc.modifier)) {
      throw new ProofCheckException("ODE proof must have at least one non-ghost equation")
    }
    val fml = proveODE.conclusion
    def sameTimeVar(x: Variable, y: Variable): Boolean = {
      (x == y && x.index.isEmpty) || // if not SSA vars
      (x.name == y.name && x.index.contains(0)  && y.index.isEmpty) || // if SSA vars 1
      (x.name == y.name && x.index.isDefined  && y.index.contains(x.index.get-1))// if SSA vars 1
    }
    theMod.foreach({case DomModify(VarPat(x, _), f) =>
      val asgn = con.getAssignments(x)
      if (!asgn.exists({case Equal(y: Variable, Number(n)) if n.toInt == 0 && sameTimeVar(x, y) => true case _ => false}))
        throw ProofCheckException(s"Duration variable $x must be initialized to 0 before ODE")
    })
    (proveODE, fml)

  }

  /** @return equivalent formula of f, with shape [a]P */
  private def asBox(f: Formula): Box = {
    f match {
      case b: Box => b
      case _ => Box(Dual(Test(f)), True)
    }
  }

  /** @return equivalent formula of f, with shape <a>P */
  private def asDiamond(f: Formula): Diamond = {
    f match {
      case b: Diamond => b
      case _ => Diamond(Test(f), True)
    }
  }


  /** @TODO: These should use unification, see [[Context]] */
  /** @return unification result of p and q, if any */
  private def unifyFml(p: Formula, q: Formula): Option[Formula] = {
    if (p == q) Some(p) else None
  }

  /** @return unification result of formulas, if any. */
  private def unifyFmls(ps: Seq[Formula]): Option[Formula] = {
    ps match {
      case Nil => None
      case p :: Nil => Some(p)
      case p :: ps => unifyFmls(ps) match {
        case None => None
        case Some(q) => unifyFml(p, q)
      }
    }
  }

  /** @return Box formula which runs programs of [[p]] first, then programs of [[b]]*/
  private def concatBox(p: Formula, q: Formula): Formula = {
    (p, q) match {
      case (True, _) => q
      case (_, True) => p
      case (Box(a, True), Box(b, q1)) => Box(Compose(a, b), q1)
      case (Box(a, True), q) => Box(Compose(a, Dual(Test(q))), True)
      case (Box(a, p1), Box(b, q1)) => Box(Compose(a, Compose(Dual(Test(p1)), b)), q1)
      case (p, Box(b, q1)) => Box(Compose(Dual(Test(p)), b), q1)
      case (Box(a, p1), q) => Box(Compose(a,Compose(Dual(Test(p1)), Dual(Test(q)))), True)
    }
  }

  /** unzip triples */
  private def unzip3[T1,T2,T3](seq:List[(T1,T2,T3)]):(List[T1],List[T2],List[T3]) = {
    seq match {
      case Nil => (Nil, Nil, Nil)
      case (x, y, z):: xyzs =>
        val (xs, ys, zs) = unzip3(xyzs)
        (xs.+:(x), ys.+:(y), zs.+:(z))
    }
  }

  /** zip triples */
  private def zip3[T1,T2,T3](xs:List[T1],ys:List[T2],zs:List[T3]):List[(T1,T2,T3)] = {
    (xs, ys, zs) match {
      case (Nil, Nil, Nil) => Nil
      case (x :: xs, y :: ys, z :: zs) => (x, y, z) :: zip3(xs, ys, zs)
      case _ => throw new Exception("Mismatched lengths in zip3")
    }
  }

  /** Check a proof, or list of statements.
    * @return final context and conclusion, else raises. */
  def apply(con: Context, p: Statements): (Context, Formula) = {
    apply(con, Block(p))
  }

  /** Collect disjuncts only down the right side, rather than *all* disjuncts. This allows us to support case analyses
   * where some branches may be disjunctions */
  private def disjoin(fml: Formula, k: Int): List[Formula] = {
    (fml, k) match {
      case (_, 1) => fml :: Nil
      case (Or(l, r), _) =>l :: disjoin(r, k-1)
      case (_, _) => throw ProofCheckException(s"Not enough branches in case statement, disjunct $fml unmatched")
    }
  }

  /** @return unit if the conclusion of selector [[sel]] has the same cases as the [[branches]], i.e. if our case analysis
    * has exactly the right cases expected by the formula that we case-analyze */
  private def compareCasesToScrutinee(con: Context, sel: Selector, branches: List[Expression]): Unit = {
    // Goal formala "true" should be ignored, case selector should not be "default"
    methodAssumptions(con: Context, sel: Selector, True) match {
      case fml :: Nil =>
        // TODO: Support cases with non-ground patterns. Improve error messages for case where right-handed split produces too few cases but exhaustive split gives too many
        // Heuristic matching: split disjuncts based on number of cases.
        // If exhaustive split gives the expected number of cases, use that. Else split down the right-hand side
        // until we peel off the right number of cases.
        val disj = FormulaTools.disjuncts(fml)
        if (disj.length == branches.length && disj.toSet != branches.toSet)
          throw ProofCheckException("Switch statement branches differ from scrutinee")
        else if (disj.length != branches.length) {
          val kDisj = disjoin(fml, branches.length)
          if (kDisj.toSet != branches.toSet)
            throw ProofCheckException(s"Switch statement with scrutinee $sel expects branches $kDisj but got $branches")
        }
      case fmls => throw ProofCheckException("Switch expected scrutinee to match exactly one formula, but matches: " + fmls)
    }
  }

  /** @return  (c1, f) where c1 is the elaboration of s (but not con) into a context and f is the conclusion proved
  * by that elaborated program */
  def apply(con: Context, s: Statement): (Context, Formula) = {
    s match {
      case Assert(_ , f, m) =>
        val elabF = con.elaborate(f)
        apply(con, elabF, m)
        (Context(s), Box(Dual(Test(elabF)), True))
      case Note(x , pt,  conclusion) =>
        val res = ForwardProofChecker(con, pt)
        if (conclusion.isDefined && conclusion.get != res) {
          throw ProofCheckException(s"Note $x expected conclusion ${conclusion.get}, got $res")
        }
        (Context(Note(x, pt, Some(res))), res)
      case Block(ss) =>
        val (c, fs) =
          ss.foldLeft[(Context, List[Formula])](Context.empty, List()){case ((acc, accF), s) =>
            val (cc, ff) = apply(con.:+(acc.s), s)
            (acc.:+(cc.s), accF.:+(ff))
          }
        val ff = fs.reduceRight(concatBox)
        (c, ff)
      case BoxChoice(left: Statement, right: Statement) =>
        val ((sl, fl), (sr, fr)) = (apply(con, left), apply(con, right))
        val (Box(a, p1), Box(b, p2)) = (asBox(fl), asBox(fr))
        val p = unifyFml(p1, p2).getOrElse(throw new ProofCheckException("Could not unify branches of choice"))
        val ss = BoxChoice(sl.s, sr.s)
        (Context(ss), Box(Choice(a,b), p))
      case Switch(sel, branches: List[(Expression, Expression, Statement)]) =>
        // @TODO: proper expression patterns not just formulas
        val defaultVar = Variable("anon")
        val (patterns, conds, bodies) = unzip3(branches)
        sel match {
          case None => if (!exhaustive(conds)) throw ProofCheckException("Inexhaustive match in switch statement")
          case Some(sel) => compareCasesToScrutinee(con, sel, branches.map(_._2))
        }
        val (cons, fmls) = branches.map(cb => {
          val v = cb._1 match {case vv: Variable => vv case _ => defaultVar}
          val (c, f) = apply(con.add(v, cb._2.asInstanceOf[Formula]), cb._3)
          (c, concatBox(Box(Test(cb._2.asInstanceOf[Formula]), True), f))}
          ).unzip
        val (as, ps) = fmls.map(asBox).map{case Box(a,p) => (Dual(a),p)}.unzip
        val p = unifyFmls(ps).getOrElse(throw ProofCheckException("Switch branches failed to unify"))
        (Context(Switch(sel, zip3(patterns, conds,cons.map(_.s)))), Box(Dual(as.reduceRight(Choice)), p))
      case While(x , j, s) =>
        val kc = con.:+(Assume(x, j))
        val (Context(sa), fa) = apply(kc, s)
        val ss = While(x, j, sa)
        val Diamond(a, p) = asDiamond(fa)
        val fml = Diamond(Loop(a), p)
        (Context(ss), fml)
      case BoxLoop(s: Statement, _) =>
        con.lastFact match {
          case None => throw ProofCheckException(s"No invariant found in $con")
          case Some((kName, kFml)) =>
            val progCon = BoxLoopProgress(BoxLoop(s, Some((kName, kFml))), Triv())
            val (ss, f) = apply(con.:+(progCon), s)
            val Box(a,p) = asBox(f)
            val res = BoxLoop(ss.s, Some((kName, kFml)))
            val ff = Box(Loop(a), p)
            val lookup = Context(ss.s).lastFact
            lookup match {
              case None => throw ProofCheckException(s"Inductive step does not prove invariant")
              case Some((kName2, kFml2)) if kFml != kFml2 =>
                throw ProofCheckException(s"Inductive step $kFml2 and invariant $kFml differ")
              case Some(kFml2) => (Context(res), ff)
            }
        }
      case pode: ProveODE =>
        val (x, y) = apply(con, pode)
        (Context(x), y)

      // @TODO: LetFun and Match should be checked in earlier passes?
      case lf: LetFun => admitLetFun(con, lf); (Context(lf), True)
      case Match(pat, e) =>
        try {
          UnificationMatch(pat, e);
          (Context(Match(pat, e)), True)
        } catch {
          case e: ProverException => throw ProofCheckException(s"Pattern match $pat = $e fails to unify")
        }
      case Ghost(s) =>
        // @TODO: May need to apply/eliminate/rewind SSA assignments in order to achieve valid scope
        // @TODO: Probably need isGhost flag to filter out unwanted assignments
        val (ss, f) = apply(con, s)
        val taboo = VariableSets(ss).boundVars
        val fv = StaticSemantics(f).fv
        if (taboo.intersect(fv.toSet).nonEmpty) {
          throw ProofCheckException(s"Ghost variable assignment escapes scope in ghost statement $f")
        }
        (Context(Ghost(ss.s)), True)
      case InverseGhost(s: Statement) =>
        val (ss, f) = apply(con, s)
        (Context(InverseGhost(ss.s)), f)
      case PrintGoal(msg) => println(s"[DEBUG] $msg: \n$con\n"); (con.:+(s), True)
      case Was(now, was) =>
        val (ss, f) = apply(con, now)
        (Context(Was(ss.s, was)), f)
      case Phi(s) =>
        val (ss, f) = apply(con, s)
        (Context(Phi(ss.s)), f)
      // Proofs that succeed unconditionally
      case Modify(VarPat(x, _), rhs) =>
        // @TODO: Needs to check ghostery
        if (SSA) {
          val n = x.name
          val xIdx = x.index.getOrElse(-1)
          val freshVar = con.fresh(n)
          val yIdx = freshVar.index.getOrElse(-1)
          if ((yIdx > xIdx)) {
            throw ProofCheckException(s"Assignment to $x was not in static-single-assignment form")
          }
        }
        rhs match {
          case Left(f) =>
            if (SSA && StaticSemantics(f).contains(x)) {
              throw ProofCheckException(s"Assignment to $x was not admissible")
            }
            (Context(s), Box(Assign(x,f), True))
          case Right(_) => (Context(s), Box(AssignAny(x), True))
        }
      case Assume(pat, f) =>
        val elabF = con.elaborate(f)
        (Context(s), Box(Test(elabF), True))
      case _: Triv | _: Label => (Context(s), True)
    }
  }
}
