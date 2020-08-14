/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/** A context is used during proof-checking and elaboration or transformation passes in order to track assumptions.
  * In Kaisar, contexts also track changes to program variables, line labels, and local definitions of function symbols.
  * Because Kaisar contexts must entirely remember the structure of a proof, we reuse the proof data structure as a
  * context.
  *
  * In practice, contexts differ thusly from a "usual" proof object:
  * 1) During proof-checking, assertions and lemmas in a context have already been proven, so their proofs need not
  *  be re-executed.
  * 2) During elaboration or proof-checking, optional annotations may be automatically filled in for a context.
  *    For example, the result of a [[Note]] lemma is inferred in the [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofChecker]]
  * 3) Contexts may introduce meta nodes which do not exist in proofs, but are helpful for proof checking.
  *   For example [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.BoxLoopProgress]] remembers the entirety of a loop while its
  *   body is being processed.
  *
  * @author Brandon Bohrer
  * @see [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof]]
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context.Finder
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{SubstitutionHelper, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

case class Context(s: Statement) {
  import Context._
  var outer: Context = this
  var ghostStatus: GhostMode = NonGhostMode

  def withOuter: Context = {
    val x = clone
    x.outer = x
    x
  }

  def reapply(s: Statement): Context = {
    val x = Context(s)
    x.ghostStatus = ghostStatus
    x.outer = outer
    x
  }

  override def clone: Context = {
    val x = Context(s)
    x.ghostStatus = ghostStatus
    x.outer = outer
    x
  }

  def isGhost: Boolean = (ghostStatus == ForwardGhostMode)
  def isInverseGhost: Boolean = (ghostStatus == InverseGhostMode)
  def withGhost: Context = {
    val gc: Context = this.clone
    gc.ghostStatus = ForwardGhostMode
    gc
  }

  def withInverseGhost: Context = {
    val gc: Context = this.clone
    gc.ghostStatus = InverseGhostMode
    gc
  }

  // @TODO: Search for "last" location
  def location: Option[Int] = s.location

  def --(other: Context): Context = {
    def fail = throw new Exception(s"Context $other is not a subcontext of $this")
    (this.s, other.s) match {
      case (s, Triv()) => Context(s)
      case (Block(ss1), Block(ss2)) =>
        if (ss2.length > ss1.length) fail
        else if (ss2.isEmpty) Context(Block(ss1))
        else {
          val lrs = ss1.zip(ss2).dropWhile({ case (l, r) => l == r }).map({ case (l, r) => Context(l).--(Context(r)) })
          val lrStatement = lrs.foldLeft(Context.empty)({ case (l, r) => l.:+(r.s) })
          if (ss1.length >= ss2.length)
            lrStatement.:+(Block(ss1.drop(ss2.length)))
          else lrStatement
        }
      case (Block(l), r) if l.nonEmpty && l.head == r => Context(Block(l.tail))
      // Only works if "other" is making progress on *this* switch statement
      case (switch: Switch, switchPr: SwitchProgress) if switch == switchPr.switch =>
        // Subtract the progress of r from the branch where progress is being made.
        Context(switch.pats(switchPr.onBranch)._3) -- Context(switchPr.progress)
      case (bc: BoxChoice, bcPr: BoxChoiceProgress) if bc == bcPr.bc =>
        if (bcPr.onBranch == 0)
          Context(bc.left) -- Context(bcPr.progress)
        else
          Context(bc.right) -- Context(bcPr.progress)
      case (l, r) => if (l == r) Context.empty else fail
    }
  }

  /** Add s to the "end" of the context. */
  def :+(other: Statement): Context = {
    s match {
      case _: Triv  => reapply(other)
      /* We are processing "pr" and simply remembering the loop "bl" while we do so.
       * the newly-processed "s" should be part of "pr". */
      case BoxLoopProgress(bl, pr) => reapply(BoxLoopProgress(bl, reapply(pr).:+(other).s))
      case SwitchProgress(switch, onBranch, pr) => reapply(SwitchProgress(switch, onBranch, reapply(pr).:+(other).s))
      case BoxChoiceProgress(bc, onBranch, pr) => reapply(BoxChoiceProgress(bc, onBranch, reapply(pr).:+(other).s))
      case Block(ss) =>
        // recursively handle boxloopprogress inside of sequence
        val (rest, last) = (ss.dropRight(1), reapply(ss.last).:+(other).s)
        reapply(KaisarProof.block(rest :+ last))
      case sl => reapply(Block(List(sl, other)))
    }
  }

  /** Add an assumption to the context */
  def add(x: Ident, fml: Formula): Context = {
    :+(Assume(x, fml))
  }

  /** The set of function symbols defined in a statement. This includes proofs which are defined under a branch or under
    * a binder. */
  def signature: Map[Function, LetFun] = {
    s match {
      case lf: LetFun => Map(lf.asFunction -> lf)
      case Block(ss) => ss.flatMap(s => Context(s).signature).toMap
      case BoxChoice(l, r) => Context(l).signature ++ Context(r).signature
      case Switch(sel, pats) => pats.map(_._3).flatMap(Context(_).signature).toMap
      case Ghost(s) => Context(s).signature
      case Was(now, was) => Context(now).signature
      case While(_, _, body) => Context(body).signature
      case BoxLoop(body, _) => Context(body).signature
      case BoxLoopProgress(bl, progress) => Context(progress).signature
      case BoxChoiceProgress(bl, i, progress) => Context(progress).signature
      case SwitchProgress(bl, i, progress) => Context(progress).signature
      case _: Triv | _: Assume | _: Assert | _: Note | _: PrintGoal | _: InverseGhost | _: ProveODE | _: Modify
           | _: Label | _: Match => Map()
    }
  }

  /** Return all assignments which mention any variant of "x" */
  /* @TODO (soundness): searchAll needs to maintain a list of "taboo" variables that have been bound after the 'current' point.
  *    In SSA style, this will only be Phi variables which get bound multiple times. Filter out any taboo variables, but don't
  *   consider it an error to search for them. */
  /* @TODO (soundness): The soundness of this function is questionable. It *may* be sound for SSA, but certainly not
  *    for arbitrary contexts. */
  def getAssignments(x: Variable, isSound: Boolean = true): List[Formula] =
    withOuter.searchAll(
      {case (v@BaseVariable(xx, idx, _), Equal(BaseVariable(xxx, idxx,_), f), true) if x.name == xx && xx == xxx && idx == idxx => true
      // @TODO: Indices get renamed here, but is that correct?
      case (v@BaseVariable(xx, idx, _), Equal(BaseVariable(xxx, idxx,_), f), true) if x.name == xx && xx == xxx  => true
     case _ => false
      }, Set(), isSound).map(_._2)
  
  /** Look up definitions of a proof variable, starting with the most recent. */
  /** @TODO: Soundness: Is this sound for SSA? What happens when a free variable of a fact is modified after the fact is proved? */
  def searchAll(f: Finder, tabooProgramVars: Set[Variable], isSound: Boolean): List[(Ident, Formula)] = {
    val fAdmiss: Finder = ({case (x, y, b) =>
      val admissible = !isSound || StaticSemantics(y).fv.toSet.intersect(tabooProgramVars).isEmpty
      admissible && f(x, y,b)})
    s match {
      case _: Triv => Nil
      case Assume(x, g) => Context.matchAssume(x, g).filter({ case (x, y) => fAdmiss(x, y, false)}).toList
      case Assert(x, g, _) => Context.matchAssume(x, g).filter({ case (x, y) => fAdmiss(x, y, false)}).toList
      case Note(x, _, Some(g)) => if (fAdmiss(x, g, false)) List((x, g)) else Nil
      // While unannotated Note's are allowed in contexts (for transformation passes), the lookup has to use a dummy value
      case Note(x, _, None) => if (fAdmiss(x, KaisarProof.askLaterP, false)) List((x, KaisarProof.askLaterP)) else Nil
      case mod: Modify => findAll(mod, f)
      case Block(ss) =>
        def iter(ss: List[Statement], f: Finder, tabooProgramVars: Set[Variable]): List[(Ident, Formula)] = {
          ss match {
            case Nil => Nil
            case (s: Phi) :: ss =>
              val left =
                reapply(s.asgns).searchAll(f, tabooProgramVars, isSound).filter({case (yx, yf) =>
                  val surrounding = Block(ss.reverse)
                  val t = VariableSets(surrounding)
                  val inter = t.tabooVars.intersect(StaticSemantics(yf).fv.toSet)
                  inter.isEmpty})
              val ff: Finder = ({
                case ((x: Ident, fml: Formula, b: Boolean)) => fAdmiss(x, Context.substPhi(s, fml), b)
              })
              val taboos = tabooProgramVars ++ VariableSets(s).boundVars
              left ++ iter(ss, ff, taboos)
            case s :: ss =>
              val left =
                reapply(s).searchAll(f, tabooProgramVars, isSound) match {
                  case ((yx, yf)) :: _ =>
                    val surrounding = Block(ss.reverse)
                    val t = VariableSets(surrounding)
                    val inter = t.tabooVars.intersect(StaticSemantics(yf).fv.toSet)
                    // Prevent ghost variables from escaping scope, unless we're turning off soundness checks or we
                    // are also a ghost.
                    if (inter.nonEmpty && isSound && !isGhost) {
                      throw ProofCheckException(s"Fact $yx inaccessible because ghost variable(s) $inter would escape their scope")
                    }
                    List((yx, yf))
                  case Nil => Nil
                }
              val taboos = tabooProgramVars ++ VariableSets(s).boundVars
              left ++ iter(ss, f, taboos)
          }
        }
        iter(ss.reverse, f, tabooProgramVars)
      case BoxChoice(l, r) => reapply(l).searchAll(f, tabooProgramVars, isSound ) ++ reapply(r).searchAll(f, tabooProgramVars, isSound)
      case Switch(sel, pats) =>
        val or: ((Ident, Formula), (Ident, Formula)) => (Ident, Formula) = {
          case ((k1, v1), (k2, v2)) =>
            if (k1 != k2) throw ProofCheckException("recursive call found formula twice with different names")
            else if (v1 == v2) (k1, v1) // optimize identical branches
            else (k1, Or(v1, v2))
        }
        val fmls = pats.flatMap({ case (v, e, s) => reapply(s).searchAll(f, tabooProgramVars, isSound) })
        if (fmls.isEmpty) Nil
        else List(fmls.reduceRight(or))
      case Ghost(s) => reapply(s).withGhost.searchAll(f, tabooProgramVars, isSound)
      // While phi nodes are "ghost" in the sense that they do not appear in the source program, we should allow ProgramVar() selectors
      // to select the equalities introduced by phi nodes.
      case Phi(s) => reapply(s).withInverseGhost.searchAll(f, tabooProgramVars, isSound)
      /* @TODO: Somewhere add a user-friendly message like s"Formula $f should not be selected from statement $s which is an inverse ghost" */
      case InverseGhost(s) => Nil
      case po: ProveODE => findAll(po, po.ds, f) ++ findAll(po.dc, f)
      case Was(now, was) => reapply(was).searchAll(f, tabooProgramVars, isSound)
      case _: Label | _: LetFun | _: Match | _: PrintGoal => Nil
      case While(_, _, body) => reapply(body).searchAll(f, tabooProgramVars, isSound)
      case BoxLoop(body, ih) =>
        val matchHere = ih match {case Some((ihVar, ihFml)) if fAdmiss(ihVar, ihFml, false) => List((ihVar, ihFml)) case _ => Nil}
        matchHere ++ reapply(body).searchAll(f, tabooProgramVars, isSound)
      case BoxLoopProgress(BoxLoop(bl, Some((ihVar, ihFml))), progress) =>
        val ihMatch = if(fAdmiss(ihVar, ihFml, false)) List((ihVar, ihFml)) else List()
        ihMatch ++ reapply(progress).searchAll(f, tabooProgramVars, isSound)
      case SwitchProgress(switch, onBranch, progress) =>
        val (x, fml: Formula, e) = switch.pats(onBranch)
        val defaultVar = Variable("anon")
        val v = x match {case vv: Variable => vv case _ => defaultVar}
        val branchMatch = if (fAdmiss(v, fml, false)) List((v, fml)) else List()
        branchMatch ++ reapply(progress).searchAll(f, tabooProgramVars, isSound)
      case BoxChoiceProgress(bc, onBranch, progress) =>
        reapply(progress).searchAll(f, tabooProgramVars, isSound)
    }
  }


  /** Find all fact bindings which satisfy [[finder]] in statement [[mod]]
    *
    * @param mod     A [[Modify]] statement which is searched for bindings
    * @param finder  A user-supplied search predicate
    * @return all bindings which satisfy [[finder]], starting with the most recent binding (i.e. variable's current value) */
  private def findAll(mod: Modify, finder: Finder): List[(Ident, Formula)] = {
    mod match {
      case Modify(TuplePat(pat :: pats), Left(Pair(l, r))) =>
        val left = findAll(Modify(pat, Left(l)), finder)
        val right = findAll(Modify(TuplePat(pats), Left(r)), finder)
        left ++ right
      /* Deterministic assignment that was annotated with a proof variable name for the introduced equality */
      case Modify(VarPat(x, Some(p)), Left(f)) if (finder(p, Equal(x, f), false)) =>
        // Note: Okay to return x=f here because admissibilty of x:=f is ensured in SSA and checked in ProofChecker.
        List((p, Equal(x, f)))
      /* Deterministic assignment which was never annotated with a proof variable name to remember the introduced equality */
      case Modify(VarPat(x, None), Left(f)) if (finder(x, Equal(x, f), true)) =>
        /* @TODO (usability): If another recursive call finds a match for "finder", return that other match. But if *no*
             branch succeeds, somebody, somewhere should give the user an error message like
             "Ghost variable $x inaccessible because it would escape its scope" */
        // Hide ghost statements except when accessed from another ghost context.
        if (isGhost && !outer.isGhost) {
          List()
        } else
          List((x, Equal(x, f)))
      case Modify(VarPat(x, Some(_)), Right(())) =>
        throw ProofCheckException("Nondeterministic assignment pattern should not bind proof variable")
      case Modify(_, _) => List()
    }
  }

  /** Find all fact and program variable bindings which satisfy [[finder]] in statement [[ds]]
    *
    * @param odeContext ODE proof in which ds appears
    * @param ds A [[DiffStatement]] statement which is searched for bindings
    * @param f  A user-supplied search predicate
    * @return all bindings which satisfy [[finder]] */
  private def findAll(odeContext: ProveODE, ds: DiffStatement, f: Finder): List[(Ident, Formula)] = {
    ds match {
      case AtomicODEStatement(AtomicODE(xp, e), solIdent) if(!this.isInverseGhost)=>
        // Can't determine exact solution until SSA pass, but we want to use this function in earlier passes, so just check
        // whether "fake" solutions exist already
        odeContext.bestSolutions match {
          case Some(sols) =>
            val solMap = sols.toMap
            val (ident, isUnnamed) = solIdent match {case Some(id) => (id, false) case None => (xp.x, true)}
            if (solMap.contains(xp.x)) {
              val eqFact = Equal(xp.x, solMap(xp.x))
              val fullFact = odeContext.timeVar match { case None => eqFact case Some(tvar) => And(eqFact, GreaterEqual(tvar, Number(0)))}
              // Search using full fact and explicit name if possible
              if (f(ident, fullFact, isUnnamed))
                List((ident, fullFact))
              // To better support ProgramVar lookups, always try f() with *just* the assignment fact as well, but pull
              // a fast one and return the whole fact
              else if (!isUnnamed && f(xp.x, eqFact, true)) List((xp.x, eqFact)) else List()
            } else List()
          case None => List()
        }
      case AtomicODEStatement(dp, _) => List()
      case DiffProductStatement(l, r) => findAll(odeContext, l, f) ++ findAll(odeContext, r, f)
      case DiffGhostStatement(ds) => withGhost.findAll(odeContext, ds, f)
      case InverseDiffGhostStatement(ds) => withInverseGhost.findAll(odeContext, ds, f)
    }
  }


  /** Find all fact bindings which satisfy [[finder]] in statement [[dc]]
    *
    * @param dc A [[DomainStatement]] statement which is searched for bindings
    * @param f  A user-supplied search predicate
    * @return all bindings which satisfy [[finder]] */
  private def findAll(dc: DomainStatement, f: Finder): List[(Ident, Formula)] = {
    dc match {
      case DomAssume(x, fml) if !isInverseGhost => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList
      case DomAssume(x, fml) => Nil
      case DomAssert(x, fml, _ ) => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList
      case DomAnd(l, r) => findAll(l, f) ++ findAll(r, f)
      case DomWeak(dc) =>
        withInverseGhost.findAll(dc, f) match {
          case fml :: _ => throw ProofCheckException(s"Weakened domain constraint $dc binds formula $fml, should not be selected")
          case Nil => Nil
        }
      case DomModify(ap, term) => reapply(Modify(ap, Left(term))).findAll(f)
    }
  }

  // top-level search function wrapper.
  private def findAll(f: Finder): List[(Ident, Formula)] = {
    withOuter.searchAll(f, Set(), isSound = true)
  }

  /* Get most recent formula (if any), bound to identifier [[id]]
  * @param wantProgramVar search exclusively for unannotated assignments x:=f rather than facts named "x" */
  def get(id: Ident, wantProgramVar: Boolean = false, isSound: Boolean = true): Option[Formula] = {
    // gotProgramVar is true only for unannotated assignment statements.
    val f: ((Ident, Formula, Boolean)) => Boolean = {
      case (x: Ident, v: Formula, gotProgramVar) =>
        if (wantProgramVar && gotProgramVar) {
          val Equal(y, f) = v
          id == y
        } else if (wantProgramVar) {
          false
        } else {
          id == x && !gotProgramVar
        }
    }
    withOuter.searchAll(f, Set(), isSound).map(_._2).headOption
  }
  def getHere(id: Ident, wantProgramVar: Boolean = false): Option[Formula] = get(id, wantProgramVar).map(elaborate)

  /** Used in proof statements such as ProveODE which have not only implicit assumptions but which need to consider
    * immediately preceding assignments. The lastBlock can include straight-line assignments and facts, which may
    * appear ghosted or unghosted.  */
  private def lastStatements(taboos: Set[Variable] = Set()): List[Statement] = {
    s match {
      case Assume(x, f) => if (StaticSemantics(f).fv.intersect(taboos).toSet.isEmpty) List(s) else Nil
      case Assert(x, f, _) => if (StaticSemantics(f).fv.intersect(taboos).toSet.isEmpty) List(s) else Nil
      case Modify(VarPat(x, _), Left(f)) => if (StaticSemantics(f).+(x).intersect(taboos).toSet.isEmpty) List(s) else Nil
      case Modify(VarPat(x, _), Right(_)) => if (!taboos.contains(x)) List(s) else Nil
      case Note(x, pt, Some(fml)) => if(StaticSemantics(fml).fv.intersect(taboos).toSet.isEmpty) List(s) else Nil
      case Phi(asgns) =>
        val res = reapply(asgns).lastStatements(taboos)
        res.map(Phi)
      case Ghost(s) =>
        val res = reapply(s).lastStatements(taboos)
        res.map({case g: Ghost => g case s: Statement => Ghost(s)})
      case Block(ss) =>
        ss.foldRight[(List[Statement], Set[Variable], Boolean)]((List(), taboos, false))({case (s, (acc, taboos, done)) =>
          if (done) (acc, taboos, done)
          else {
            val res = reapply(s).lastStatements(taboos)
            if (res.isEmpty) (Nil, taboos, true)
            else {
              val tt = taboos ++ VariableSets(s).boundVars
              (res ++ acc, tt, false)
            }}})._1
      case Was(now, was) => reapply(now).lastStatements(taboos)
      case _: PrintGoal => List(s)
      case _ =>
        Nil
    }
  }

  /** Used in proof statements such as ProveODE which have not only implicit assumptions but which need to consider
    * immediately preceding assignments. The lastBlock can include straight-line assignments and facts, which may
    * appear ghosted or unghosted.  */
  def lastBlock: Block = Block(lastStatements())

  // @TODO: Merge with lastStatements
    /** Used in proof statements with implicit assumptions, such as BoxLoop which implicitly finds a base case.
    * @return Most recent fact of context and context of phi assignments since the fact was bound */
  private def lastFactMobile: (Option[(Ident, Formula)], List[Phi]) = {
    s match {
      case Assume(x: Variable, f) => (Some((x, f)), Nil)
      case Assert(x: Variable, f, _) => (Some((x,f)), Nil)
      case Note(x: Variable, pt, opt) => (opt.map((x, _)), Nil)
      case Modify(VarPat(x, Some(p)), Left(f)) => (Some((p, Equal(x, f))), Nil)
      case Modify(VarPat(x, _), Left(f)) => (Some((x, Equal(x, f))), Nil)
      case BoxChoice(l, r) =>
        (Context(l).lastFactMobile, Context(r).lastFactMobile) match {
          case ((Some((kl, vl)), leftPhis), (Some((kr, vr)), rightPhis)) =>
            if (kl != kr) (None, Nil)
            // There is a last fact, but we can't come up with unique phi assignments for it, so ignore it
            else if (leftPhis != rightPhis) (None, Nil)
            // Optimize identical ors
            else if (vl == vr) (Some((kl, vl)), leftPhis)
            else (Some((kl, Or(vl, vr))), leftPhis)
          // note: if only one branch has last-fact, it would be unsound to return that fact. Instead, ignore it.
          case _ => (None, Nil)
        }
      case BoxLoop(body, _) => Context(body).lastFactMobile
      case While(_, _, body) => Context(body).lastFactMobile
      // Note: After SSA, last statement is phi node, so keep looking to find "real" node
      case Block(ss) =>
        // @TODO: Need a more general way to handle phi assignments
        ss.reverse match {
          case (phi: Phi) :: rest =>
            val (fact, phis) = rest.map(Context(_).lastFactMobile).filter(_._1.isDefined).head
            (fact, phi :: phis)
          case ss =>
            ss.map(Context(_).lastFactMobile).filter(_._1.isDefined).head
        }
      case Was(now, was) => Context(now).lastFactMobile
      case Ghost(s) => Context(s).lastFactMobile
      // Skips all meta nodes and inverse ghosts, for example
      case _ => (None, Nil)
    }
  }

  private def destabilize(f: Formula): Formula =
    SubstitutionHelper.replacesFree(f)(f => KaisarProof.getStable(f))

  /** Final elaboration step used in proof-checker or after deterritorialize pass */
  def elaborate(f: Formula): Formula = destabilize(f)

  private def unpackPairs(t: Term): List[Term] = {
    t match {
      case Nothing => Nil
      case Pair(l, r) => unpackPairs(l) ++ unpackPairs(r)
      case f => List(f)
    }
  }

  private def replaceFunctions(t: Term): Option[Term] = {
    t match {
      case f: FuncOf =>
        signature.get(f.func) match {
          case Some(lf) =>
            val elabChild = elaborateFunctions(f.child)
            val elabArgs = unpackPairs(elabChild)
            if (elabArgs.length != lf.args.length)
              throw ElaborationException(s"Function ${f.func.name} called with ${elabArgs.length}, expected ${lf.args.length}")
            val argMap = lf.args.zip(elabArgs).toMap
            Some(SubstitutionHelper.replacesFree(lf.e)({case (v: Variable) => argMap.get(v) case _ => None }).asInstanceOf[Term])
          case None =>
            KaisarProof.getAt(f) match {
              case Some((trm, lr)) =>
                Some(KaisarProof.makeAt(elaborateFunctions(trm), LabelRef(lr.label, lr.args.map(elaborateFunctions))))
              case None =>
                if (KaisarProof.isBuiltinFunction(f.func)) {
                  val elabChild = elaborateFunctions(f.child)
                  Some(FuncOf(f.func, elabChild))
                } else
                  throw ElaborationException(s"Unknown function ${f.func}")
            }
        }
      case _ => None
    }
  }

  /** Elaborate user-defined functions in an expression*/
  def elaborateFunctions(f: Term): Term = SubstitutionHelper.replacesFree(f)(f => replaceFunctions(f))
  def elaborateFunctions(fml: Formula): Formula = SubstitutionHelper.replacesFree(fml)(f => replaceFunctions(f))

  def lastFact: Option[(Ident, Formula)] = {
    val (fml, phis) = lastFactMobile
    val mapped = fml.map({case ((k,fact)) => (k, phis.foldLeft(fact)((fml, phi) => Context.substPhi(phi, fml)))})
    val res =  mapped.map({case (k, v) => (k, destabilize(v))})
    res
  }

  /** Does the context contain a fact named [[id]]? */
  def contains(id: Ident): Boolean = get(id).isDefined

  /** return all facts that unify with a given pattern */
  def unifyAll(pat: Expression): List[(Ident, Formula)] = {
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, fml: Formula, false) =>
      try {
        UnificationMatch(pat, fml)
        true
      } catch {
        case _: ProverException => false
      }
    case _ => false}
    searchAll(f, Set(), isSound = true)
  }
  /** Return first fact that unifies with a pattern, if any. */
  def unify(pat: Expression): Option[(Ident, Formula)] = unifyAll(pat).headOption

  // Base name used for fresh variables generated during proof when no better variable name is available.
  private val ghostVar: String = "ghost"

  /** @return A proof variable name which is not bound in the context. */
  def fresh(ident: String = ghostVar): Ident = {
    var i = 0
    while(contains(Variable(ident + i))) {
      i = i + 1
    }
    Variable(ident + i)
  }

  /**  Bind the next ghost variable to formula f */
  def ghost(f: Formula): Context = add(fresh(), f)
}

object Context {
  // Type of user-supplied predicates used to search the context.
  // fact identifier, fact formula, whether fact is from an assignment
  type Finder = ((Ident, Formula, Boolean)) => Boolean

  sealed trait GhostMode
  case object NonGhostMode extends GhostMode
  case object ForwardGhostMode extends GhostMode
  case object InverseGhostMode extends GhostMode

  def empty: Context = Context(Triv())

  /** Do the head constructors of two expressions match? */
  private def sameHead(e: Expression, f: Expression): Boolean = {
    (e, f) match {
      case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
        bcf1.reapply(bcf2.left, bcf2.right) == bcf2
      case (ucf1: UnaryCompositeFormula, ucf2: UnaryCompositeFormula) =>
        ucf1.reapply(ucf2.child) == ucf2
      // No matching in quantified vars or program, so reapply to q1/m1
      case (q1: Quantified, q2: Quantified) => q1.reapply(q1.vars, q2.child) == q2
      case (m1: Modal, m2: Modal) => m1.reapply(m1.program, m2.child) == m2
      case _ => false
    }
  }

  /** @param e the left-hand side of an assumption statement, which is a pattern that binds fact variables
    * @param f the right-hand side of an assumption statement, which is a formula expression
    * @return the set of fact bindings introduced by an assumption statement */
  private def matchAssume(e: Expression, f: Formula): Map[Ident, Formula] = {
    e match {
      // [[Nothing]] represents an assumption with no left-hand side, which cannot be referenced by name.
      case Nothing => Map()
      case BaseVariable(x, _, _) => Map(Variable(x) -> f)
      case _ =>
        if (!sameHead(e, f))
          throw ProofCheckException(s"Pattern $e does not match formula $f")
        (e, f) match {
          case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
            matchAssume(bcf1.left, bcf2.left) ++ matchAssume(bcf1.right, bcf2.right)
          case (ucf1: BinaryCompositeFormula, ucf2: BinaryCompositeFormula) =>
            matchAssume(ucf1.left, ucf2.left)
          case (q1: Quantified, q2: Quantified) => matchAssume(q1.child, q2.child)
          case (m1: Modal, m2: Modal) => matchAssume(m1.child, m2.child)
        }
    }
  }

  // Rename formula according to assignment from an SSA Phi node
  private def substPhi(phi: Phi, fml: Formula): Formula = {
    val mapping = phi.reverseMap
    SubstitutionHelper.replacesFree(fml)(term => {
      (KaisarProof.getStable(term), term) match {
        case (Some(_), _) => Some(term)
        case (None, v: Variable) => mapping.get(v)
        case (None, _) => None
      }})
  }

}