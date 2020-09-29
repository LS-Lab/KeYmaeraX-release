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
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr, SubstitutionHelper, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.ProofCheckException
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction

sealed trait ContextQuery {
  def matches(x: Option[Ident], f: Formula, isAssignment: Boolean): Boolean
}
case class QProgramVar(x: Variable) extends ContextQuery {
  override def matches(yOpt: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = {
    val vars = StaticSemantics(fml)
    val allVars: Set[Variable] = (vars.fv ++ vars.bv).toSet//.++(yOpt.toSet)
    allVars.exists(y => x.name == y.name)
  }
}
case class QAssignments(x: Variable, onlySSA: Boolean) extends ContextQuery {
  override def matches(y: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = {
    isAssignment && (fml match {case Equal(z: Variable, _) => x.name == z.name case _ => false })
  }
}
case class QUnion(l: ContextQuery, r: ContextQuery) extends ContextQuery {
  override def matches(x: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean =
    l.matches(x, fml, isAssignment) || r.matches(x, fml, isAssignment)
}
case class QProofVar(x: Variable) extends ContextQuery {
  // @TODO: Make interface clear for assignments with or without identifiers
  override def matches(y: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = y.contains(x) && !isAssignment
}
case class QProofTerm(pt: ProofTerm) extends ContextQuery {
  override def matches(x: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean = false
}
case class QUnify(pat: Expression) extends ContextQuery {
  override def matches(maybeX: Option[Ident], f: Formula, isAssignment: Boolean): Boolean = {
    maybeX match {
      case Some(x) =>
        try {
          UnificationMatch(pat, f)
          true
        } catch {
          case _: ProverException => false
        }
      case None => false
    }
  }
}
case class QPhi(phi: Phi, cq: ContextQuery) extends ContextQuery {
  override def matches(x: Option[Ident], fml: Formula, isAssignment: Boolean): Boolean =
    cq.matches(x, Context.substPhi(phi, fml), isAssignment)
}

sealed trait ContextResult {
  type Item = (Option[Ident], Formula, Boolean)
  def isEmpty: Boolean = {
    this match {
      case RUnion(l, r) => l.isEmpty && r.isEmpty
      case RFailure(msg) => true
      case RSuccess(facts, assigns) => facts.isEmpty && assigns.isEmpty
    }
  }
  def nonEmpty: Boolean = !isEmpty
  def assignFact(as: Assign): Formula = Equal(as.x, as.e)
  def assignId(as: Assign): Option[Ident] = None

  def filter(p: Item => Boolean): ContextResult = {
    this match {
      case RUnion(l, r) => RUnion(l.filter(p), r.filter(p))
      case RFailure(msg) => RFailure(msg)
      case RSuccess(facts, assigns) => RSuccess(facts.filter({case (id, fml) => p(id, fml, false)}), assigns.filter(asgn => p(assignId(asgn), assignFact(asgn), true)))
    }
  }

  def foreach(p: Item => Unit): Unit = {
    this match {
      case RUnion(l, r) => l.foreach(p); r.foreach(p)
      case RFailure(msg) => ()
      case RSuccess(facts, assigns) =>
        facts.foreach({case (id, fml) => p(id, fml, false)})
        assigns.foreach(asgn => p(assignId(asgn), assignFact(asgn), true))
    }
  }

  def admissiblePart(inContext: Context, tabooProgramVars: Set[Variable]): ContextResult =
    this match {
      case _: RFailure => this
      case RUnion(l, r) => RUnion(l.admissiblePart(inContext, tabooProgramVars), r.admissiblePart(inContext, tabooProgramVars))
      case RSuccess(facts, assigns) =>
        // && cq.matches(x, y,b)
        def factFilter(id: Option[Ident], fml: Formula): Boolean = {
          val free = StaticSemantics(KaisarProof.forgetAt(fml)).fv
          inContext.isElaborationContext || free.toSet.intersect(tabooProgramVars).isEmpty
        }
        def assignFilter(as: Assign): Boolean = factFilter(assignId(as), assignFact(as))
        RSuccess(facts.filter({case (x, y) => factFilter(x, y)}), assigns.filter(assignFilter))
    }

  // @TODO: Better data structure for assignments that might also have names. matchesAssign vs matchesFact
  def matchingPart(cq: ContextQuery): ContextResult = {
    this match {
      case _: RFailure => this
      case RUnion(l, r) => RUnion(l.matchingPart(cq), r.matchingPart(cq))
      case RSuccess(facts, assigns) => RSuccess(
        facts.filter({case (id, fml) => cq.matches(id, fml, isAssignment = false)}),
        assigns.filter({case (asgn: Assign) => cq.matches(Some(asgn.x), assignFact(asgn), isAssignment = true)}))
    }
  }
  def asList: List[(Option[Ident], Formula)]
  def formulas: List[Formula] = asList.map(_._2)
  def ++(other: ContextResult): ContextResult =
    (this, other) match {
      case (_: RFailure, _) => this
      case (_, _: RFailure) => other
      case (RUnion(l, r), _) => l.++(r).++(other)
      case (_, RUnion(l, r)) => ++(l).++(r)
      case (RSuccess(factsL, assignsL), RSuccess(factsR, assignsR)) =>
        RSuccess(factsL.++(factsR), assignsL.++(assignsR))
    }
}
case class RSuccess(facts: Set[(Option[Ident], Formula)], assigns: Set[Assign] = Set()) extends ContextResult {
  override def asList: List[(Option[Ident], Formula)] = facts.toList ++ assigns.map((as: Assign) =>  (None, Equal(as.x, as.e))).toList
}
case class RFailure(msg: String) extends ContextResult {
  override def asList: List[(Option[Ident], Formula)] = Nil
}
// @TODO: May be unnecessary
// @TODO: Don't need union but do need "branch". Union should be a function.
case class RUnion(l: ContextResult, r: ContextResult) extends ContextResult {
  override def asList: List[(Option[Ident], Formula)] = l.asList ++ r.asList
}
object ContextResult {
  def unit: ContextResult = RSuccess(Set(), Set())
}

case class Context(s: Statement) {
  import Context._
  // Metadata are vars rather than constructor arguments so that pattern-matches on Context remain simple.

  // When recursively traversing a proof statement with context, [[outer]] represents the context at the beginning of
  // the recursion.
  private var outer: Context = this
  // Tracks whether the *statement* being checked appears under a Ghost or InverseGhost node.
  // This is *distinct* from whether the context statement [[s]] contains ghosts.
  private var ghostStatus: GhostMode = NonGhostMode
  // The [[isElaborationContext]] flag should be true (only) in early elaboration passes, before SSA.
  // The elaboration passes use this to disable strict SSA soundness checking and allow partial sanity checking of
  // proofs that might not succeed.
  private var _isElaborationContext: Boolean = false

  def isEmpty: Boolean = (s == Triv())

  /** Remember the current context as the [[outer]] context before a recursive traversal */
  def withOuter: Context = {
    val x = clone
    x.outer = x
    x
  }

  /** Convert input [[s]] to a context, but remember the metadata from [[this]] context */
  def reapply(s: Statement): Context = {
    val x = Context(s)
    x.ghostStatus = ghostStatus
    x.outer = outer
    x._isElaborationContext = _isElaborationContext
    x
  }

  /** Copy this context to provide persistent interface */
  override def clone: Context = {
    val x = Context(s)
    x.ghostStatus = ghostStatus
    x.outer = outer
    x._isElaborationContext = _isElaborationContext
    x
  }

  /** Are we checking a statement which appears as a forward ghost? */
  def isGhost: Boolean = (ghostStatus == ForwardGhostMode)
  /** Are we checking a statement which appears as an inverse ghost? */
  def isInverseGhost: Boolean = (ghostStatus == InverseGhostMode)
  /** Does this context represent an elaboration pass? */
  def isElaborationContext: Boolean = _isElaborationContext

  /** Clone this context with the elaboration flag set */
  def asElaborationContext: Context = {
    val ec: Context = this.clone
    ec._isElaborationContext = true
    ec
  }

  /** Clone this context but indicate that we are checking a ghost statement */
  def withGhost: Context = {
    val gc: Context = this.clone
    gc.ghostStatus = ForwardGhostMode
    gc
  }

  /** Clone this context but indicate that we are checking an inverse ghost statement */
  def withInverseGhost: Context = {
    val gc: Context = this.clone
    gc.ghostStatus = InverseGhostMode
    gc
  }

  // @TODO: Search for "last" location
  /** Recover the "current" line and column number using the position information of the underlying statement  */
  def location: Option[Int] = s.location

  /** Compute the "difference" between two contexts.  A "difference" only exists if the underlying statement of  [[other]]
    * is a "prefix" of [[this]], and consists of statements in [[this]] which remain after deleting the prefix [[other]].
    * When [[this]] is a branching proof (e.g. Switch), we consider [[other]] a prefix even if [[other]] is currently
    * proving some branch of the switch.
    * An exception is thrown if the difference does not exist. */
  def --(other: Context): Context = {
    def fail = throw TransformationException(s"Context $other is not a prefix of $this", node = s)
    if (this.s == other.s) Context.empty
    else
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
      case (Block(l), r) if l.nonEmpty  =>
        val diff = Context(l.head) -- Context(r)
        if (diff.isEmpty) Context(Block(l.tail))
        else Context(KaisarProof.block(diff.s :: l.tail))
      // Only works if "other" is making progress on *this* switch statement
      case (switch: Switch, switchPr: SwitchProgress) if switch == switchPr.switch =>
        // Subtract the progress of r from the branch where progress is being made.
        Context(switch.pats(switchPr.onBranch)._3) -- Context(switchPr.progress)
      case (bc: BoxChoice, bcPr: BoxChoiceProgress) if bc == bcPr.bc =>
        if (bcPr.onBranch == 0)
          Context(bc.left) -- Context(bcPr.progress)
        else
          Context(bc.right) -- Context(bcPr.progress)
      case (l, r) => fail
    }
  }

  /** Add s to the "end" of the context. */
  def :+(other: Statement): Context = {
    s match {
      case _: Triv  => reapply(other)
      /* We are processing "pr" and simply remembering the loop "bl" while we do so.
       * the newly-processed "s" should be part of "pr". */
      case BoxLoopProgress(bl, pr) => reapply(BoxLoopProgress(bl, reapply(pr).:+(other).s))
      case WhileProgress(wh, pr) => reapply(WhileProgress(wh, reapply(pr).:+(other).s))
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
  def signature: Map[Function, LetSym] = {
    s match {
      case lf: LetSym => Map(lf.asFunction -> lf)
      case Block(ss) => ss.flatMap(s => Context(s).signature).toMap
      case BoxChoice(l, r) => Context(l).signature ++ Context(r).signature
      case Switch(sel, pats) => pats.map(_._3).flatMap(Context(_).signature).toMap
      case Ghost(s) => Context(s).signature
      case Was(now, was) => Context(now).signature
      case While(_, _, body) => Context(body).signature
      case BoxLoop(body, _) => Context(body).signature
      case BoxLoopProgress(bl, progress) => Context(progress).signature
      case WhileProgress(wh, prog) => Context(prog).signature
      case BoxChoiceProgress(bl, i, progress) => Context(progress).signature
      case SwitchProgress(bl, i, progress) => Context(progress).signature
      case Phi(s) => Context(s).signature
      case _: Triv | _: Assume | _: Assert | _: Note | _: PrintGoal | _: InverseGhost | _: ProveODE | _: Modify
           | _: Label | _: Match => Map()
    }
  }

  /** Return all assignments which mention any variant of "x" */
  def getAssignments(x: Variable): List[Formula] =
    withOuter.searchAll(QAssignments(x, onlySSA = false), Set()).formulas

  // Return all facts which mention any SSA-variant of x
  def getMentions(x: Variable): List[Formula] =
    withOuter.searchAll(QProgramVar(x), Set()).formulas

  /** Look up definitions of a proof variable, starting with the most recent. */
  /** @TODO: Soundness: Is this sound for SSA? What happens when a free variable of a fact is modified after the fact is proved? */
  def searchAll(cq: ContextQuery, tabooProgramVars: Set[Variable]): ContextResult = {
    s match {
      case _: Triv => ContextResult.unit
      case Assume(x, g) => Context.matchAssume(x, g, s).admissiblePart(this, tabooProgramVars).matchingPart(cq)
      case Assert(x, g, _) => Context.matchAssume(x, g, s).admissiblePart(this, tabooProgramVars).matchingPart(cq)
      case Note(x, _, Some(g)) => RSuccess(Set((Some(x), g))).admissiblePart(this, tabooProgramVars).matchingPart(cq)
      // While unannotated Note's are allowed in contexts (for transformation passes), the lookup has to use a dummy value
      // @TODO: Use less dummy fact variable names/facts
      case Note(x, _, None) => RSuccess(Set((Some(x), KaisarProof.askLaterP))).admissiblePart(this, tabooProgramVars).matchingPart(cq)
      case mod: Modify => findAll(mod, cq)
      case Block(ss) =>
        def iter(ss: List[Statement], cq: ContextQuery, tabooProgramVars: Set[Variable]): ContextResult = {
          ss match {
            case Nil => ContextResult.unit
            case (s: Phi) :: ss =>
              val left =
                reapply(s.asgns).searchAll(cq, tabooProgramVars).filter({case (yx, yf, yisAssign) =>
                  val surrounding = Block(ss.reverse)
                  val t = VariableSets(surrounding)
                  val inter = t.tabooVars.intersect(StaticSemantics(yf).fv.toSet)
                  inter.isEmpty})
              val taboos = tabooProgramVars ++ VariableSets(s).boundVars
              RUnion(left, iter(ss, QPhi(s, cq), taboos))
            case s :: ss =>
              val leftMatches = reapply(s).searchAll(cq, tabooProgramVars)
              val surrounding = Block(ss.reverse)
              val t = VariableSets(surrounding)
              // @TODO: Finder needs to be able to specify verbosity level, leave out some error messages
              // @TODO: Careful that it's really okay to look up ghost assignments. Think it is okay here, needs checked elsewhere
              leftMatches.foreach({ case ((yx, yf, isAssignment)) =>
                if(yx.nonEmpty && t.tabooFacts.contains(yx.get) && !isElaborationContext && !isInverseGhost)
                  throw ProofCheckException(s"Inverse ghost fact $yx inaccessible outside of other inverse ghosts", node = s)
                })
              val taboos = tabooProgramVars ++ VariableSets(s).boundVars
              leftMatches ++ iter(ss, cq, taboos)
          }
        }
        iter(ss.reverse, cq, tabooProgramVars)
      case BoxChoice(l, r) => reapply(l).searchAll(cq, tabooProgramVars) ++ reapply(r).searchAll(cq, tabooProgramVars)
      case switch@Switch(sel, pats) =>
        val or: ((Ident, Formula), (Ident, Formula)) => (Ident, Formula) = {
          case ((k1, v1), (k2, v2)) =>
            // @TODO: happens because of ghosts on different branches. think more cleverly what to do about it
            /*if (k1 != k2) throw ProofCheckException(s"recursive call found formula twice with different names: $k1 and $k2", node = switch)
            else*/
            if (v1 == v2) (k1, v1) // optimize identical branches
            else (k1, Or(v1, v2))
        }
        val fmls = pats.map({ case (v, e, s) => reapply(s).searchAll(cq, tabooProgramVars) })
        if (fmls.isEmpty) ContextResult.unit
        else fmls.reduce(RUnion)
      case Ghost(s) => reapply(s).withGhost.searchAll(cq, tabooProgramVars)
      // While phi nodes are "ghost" in the sense that they do not appear in the source program, we should allow ProgramVar() selectors
      // to select the equalities introduced by phi nodes.
      case Phi(s) => reapply(s).withInverseGhost.searchAll(cq, tabooProgramVars)
      /* @TODO: Somewhere add a user-friendly message like s"Formula $f should not be selected from statement $s which is an inverse ghost" */
      case InverseGhost(s) => ContextResult.unit
      case po: ProveODE => RUnion(findAll(po, po.ds, cq), findAll(po.dc, cq))
      case Was(now, was) => reapply(was).searchAll(cq, tabooProgramVars)
      case _: Label | _: LetSym | _: Match | _: PrintGoal => ContextResult.unit
      case While(_, _, body) =>
        //@TODO
        // only allowed to find IH
        //reapply(body).searchAll(f, tabooProgramVars)
        ContextResult.unit
      case BoxLoop(body, ih) =>
        // only allowed to find IH
        ih match {
          case Some((ihVar, _oldIhFml, Some(ihFml))) => RSuccess(Set((Some(ihVar), ihFml))).admissiblePart(this, tabooProgramVars).matchingPart(cq)
          case Some((ihVar, ihFml, None)) => RSuccess(Set((Some(ihVar), ihFml))).admissiblePart(this, tabooProgramVars).matchingPart(cq)
          case _ => ContextResult.unit
        }
      case BoxLoopProgress(BoxLoop(bl, ihOpt), progress) => {
        val ihMatch: ContextResult = ihOpt.map({
          case ((ihVar, _oldIhFml, Some(ihFml))) => RSuccess(Set((Some(ihVar), ihFml))).admissiblePart(this, tabooProgramVars).matchingPart(cq)
          case ((ihVar, ihFml, None)) => RSuccess(Set((Some(ihVar), ihFml))).admissiblePart(this, tabooProgramVars).matchingPart(cq)
          case _ => ContextResult.unit}).getOrElse(ContextResult.unit)
        RUnion(ihMatch, reapply(progress).searchAll(cq, tabooProgramVars))
      }
      case WhileProgress(While(x, j, s), prog) =>
        val convMatch = Context.matchAssume(x, j, s).admissiblePart(this, tabooProgramVars).matchingPart(cq)
        convMatch ++ reapply(prog).searchAll(cq, tabooProgramVars)
      case SwitchProgress(switch, onBranch, progress) =>
        val (x, fml: Formula, e) = switch.pats(onBranch)
        val defaultVar = Variable("anon")
        val v = x match {case vv: Variable => vv case _ => defaultVar}
        val branchMatch = RSuccess(Set((Some(v), fml)), Set()).admissiblePart(this, tabooProgramVars).matchingPart(cq)
        branchMatch ++ reapply(progress).searchAll(cq, tabooProgramVars)
      case BoxChoiceProgress(bc, onBranch, progress) =>
        reapply(progress).searchAll(cq, tabooProgramVars)
    }
  }

  /** Find all fact bindings which satisfy [[finder]] in statement [[mod]]
    *
    * @param mod   A [[Modify]] statement which is searched for bindings
    * @param cq    A user-supplied search query
    * @return all bindings which satisfy [[finder]], starting with the most recent binding (i.e. variable's current value) */
  private def findAll(mod: Modify, cq: ContextQuery): ContextResult = {
    mod.asgns.map({case (Some(p), x, Some(f)) if (cq.matches(Some(p), Equal(x, f), isAssignment = false)) =>
      // Note: Okay to return x=f here because admissibilty of x:=f is ensured in SSA and checked in ProofChecker.
      RSuccess(Set((Some(p), Equal(x, f))), Set())
    case (None, x, Some(f)) if (cq.matches(Some(x), Equal(x, f), isAssignment = true)) =>
      /* @TODO (usability): If another recursive call finds a match for "finder", return that other match. But if *no*
           branch succeeds, somebody, somewhere should give the user an error message like
           "Ghost variable $x inaccessible because it would escape its scope" */
      // Hide ghost statements except when accessed from another ghost context.
      if (isGhost && !outer.isGhost) {
        ContextResult.unit
      } else
        RSuccess(Set(), Set(Assign(x, f)))
    case (Some(_), x, None) =>
      throw ProofCheckException("Nondeterministic assignment pattern should not bind proof variable", node = mod)
    case _ => ContextResult.unit
    }).reduce(RUnion)
  }

  /** Find all fact and program variable bindings which satisfy [[finder]] in statement [[ds]]
    *
    * @param odeContext ODE proof in which ds appears
    * @param ds A [[DiffStatement]] statement which is searched for bindings
    * @param f  A user-supplied search predicate
    * @return all bindings which satisfy [[finder]] */
  private def findAll(odeContext: ProveODE, ds: DiffStatement, cq: ContextQuery): ContextResult /*List[(Ident, Formula)] */= {
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
              if (cq.matches(Some(ident), fullFact, isUnnamed))
                RSuccess(Set((Some(ident), fullFact)), Set())
              // To better support ProgramVar lookups, always try f() with *just* the assignment fact as well, but pull
              // a fast one and return the whole fact
              else if (!isUnnamed && cq.matches(Some(xp.x), eqFact, isAssignment = true)) RSuccess(Set(), Set(Assign(xp.x, solMap(xp.x)))) else ContextResult.unit
            } else ContextResult.unit
          case None => ContextResult.unit
        }
      case AtomicODEStatement(dp, _) => ContextResult.unit
      case DiffProductStatement(l, r) => RUnion(findAll(odeContext, l, cq), findAll(odeContext, r, cq))
      case DiffGhostStatement(ds) => withGhost.findAll(odeContext, ds, cq)
      case InverseDiffGhostStatement(ds) => withInverseGhost.findAll(odeContext, ds, cq)
    }
  }


  /** Find all fact bindings which satisfy [[finder]] in statement [[dc]]
    *
    * @param dc A [[DomainStatement]] statement which is searched for bindings
    * @param cq  A user-supplied search query
    * @return all bindings which satisfy [[cq]] */
  private def findAll(dc: DomainStatement, cq: ContextQuery): ContextResult /*List[(Ident, Formula)] */ = {
    dc match {
      case DomAssume(x, fml) if !isInverseGhost => matchAssume(x, fml, dc).matchingPart(cq)
      case DomAssume(x, fml) => ContextResult.unit
      case DomAssert(x, fml, _ ) => matchAssume(x, fml, dc).matchingPart(cq)
      case DomAnd(l, r) => findAll(l, cq) ++ findAll(r, cq)
      case dw@DomWeak(dc) =>
        withInverseGhost.findAll(dc, cq) match {
          // @TODO: Better message
          case cr if cr.nonEmpty => throw ProofCheckException(s"Weakened domain constraint $dc selected result ${cq}, but selection should have been empty", node = dw)
          case cr => ContextResult.unit
        }
      case dm: DomModify => reapply(Modify(dm)).findAll(cq)
    }
  }

  // top-level search function wrapper.
  private def findAll(cq: ContextQuery): ContextResult /*List[(Ident, Formula)]*/ = {
    withOuter.searchAll(cq, Set())
  }

  /* Get most recent formula (if any), bound to identifier [[id]]
  * @param wantProgramVar search exclusively for unannotated assignments x:=f rather than facts named "x" */
  def get(id: Ident, wantProgramVar: Boolean = false, isSound: Boolean = true): Option[Formula] = {
    val cq: ContextQuery = if (wantProgramVar) QProgramVar(id) else QProofVar(id)
    withOuter.searchAll(cq, Set()).formulas.headOption
  }
  def getHere(id: Ident, wantProgramVar: Boolean = false): Option[Formula] = get(id, wantProgramVar).map(elaborateStable)

  /** Used in proof statements such as ProveODE which have not only implicit assumptions but which need to consider
    * immediately preceding assignments. The lastBlock can include straight-line assignments and facts, which may
    * appear ghosted or unghosted.  */
  private def lastStatements(taboos: Set[Variable] = Set()): List[Statement] = {
    s match {
      case Assume(x, f) => if (StaticSemantics(f).fv.intersect(taboos).toSet.isEmpty) List(s) else Nil
      case Assert(x, f, _) => if (StaticSemantics(f).fv.intersect(taboos).toSet.isEmpty) List(s) else Nil
      case mod: Modify =>
        val admissible = mod.mods.forall({
          case (x, Some(f)) => StaticSemantics(f).+(x).intersect(taboos).toSet.isEmpty
          case (x, None) => !taboos.contains(x)
          case _ => false
        })
        if (admissible) List(s) else Nil
      case Note(x, pt, Some(fml)) => if(StaticSemantics(fml).fv.intersect(taboos).toSet.isEmpty) List(s) else Nil
      case Phi(asgns) =>
        val res = reapply(asgns).lastStatements(taboos)
        res.map(Phi)
      case Ghost(s) =>
        val res = reapply(s).lastStatements(taboos)
        val mapped = res.map({case g: Ghost => g case s: Statement => Ghost(s)})
        mapped
      case Block(ss) =>
        ss.foldRight[(List[Statement], Set[Variable], Boolean)]((List(), taboos, false))({case (s, (acc, taboos, done)) =>
          if (done) (acc, taboos, done)
          else {
            val res = reapply(s).lastStatements(taboos)
            if (res.isEmpty) (acc, taboos, true)
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

  private def collectLastFact: (Option[(Ident, Formula)], List[Phi]) = {
    def unwind(wound: List[Statement]): (Option[(Ident, Formula)], List[Phi]) = {
      wound match {
        case Assert(x: Variable, f, _) :: _ => (Some((x, f)), Nil)
        case Assume(x: Variable, f) :: _ => (Some((x, f)), Nil)
        case Assert(Nothing, f, _) :: _ => (Some((unnamedVar, f)), Nil)
        case Assume(Nothing, f) :: _ => (Some((unnamedVar, f)), Nil)
        case (phi: Phi) :: rest =>
          val (fml, phis) = unwind(rest)
          (fml, phi :: phis)
        // looking up forward-ghost facts is ok
        case Ghost(s) :: ss => unwind(s :: ss)
        case s :: ss => unwind(ss)
        case Nil => (None, Nil)
      }
    }
    unwind(lastStatements().reverse)
  }

  private def finishFact(f: Formula, phis: List[Phi]): Formula = destabilize(phis.foldLeft(f)((fml, phi) => Context.substPhi(phi, fml)))

  /** The most recently proven fact in a context.
    * Fact is returned as (ident, unelaboratedFml, elaboratedFml) */
  def lastFact: Option[(Ident, Formula, Formula)] = {
    val (kFml, phis) = collectLastFact
    val triple = kFml.map({case (k, fml) => (k, fml, elaborateFunctions(fml, Triv()))})
    triple.map({case ((k,fact, elab)) => (k, finishFact(fact, phis), finishFact(elab, phis))})
  }

  def rawLastFact: Option[(Ident, Formula)] = {
    val (kFml, phis) = collectLastFact
    kFml.map({case ((k,fact)) => (k, finishFact(fact, phis))})
  }

  /** Elaborate the "stable" term tag once it is no longer needed */
  private def destabilize(f: Formula): Formula =
    SubstitutionHelper.replacesFree(f)(f => KaisarProof.getStable(f))

  // While it would be nice to do all translation steps before the proof-checker, the lastFact computations in ProofChecker
  // need "stable" markers to determine when loop base cases and inductive steps agree.
  /** Final elaboration step used in proof-checker. */
  def elaborateStable(f: Formula): Formula = destabilize(f)

  /** Optionally replace user-defined function symbols in [[t]] */
  private def replaceFunctions(t: Term, node: ASTNode = Triv()): Option[Term] = {
    t match {
      case f: FuncOf =>
        signature.get(f.func) match {
          case Some(lf) =>
            val elabChild = elaborateFunctions(f.child, node)
            val elabArgs = StandardLibrary.tupleToTerms(elabChild, node)
            if (elabArgs.length != lf.args.length)
              throw ElaborationException(s"Function ${f.func.name} called with ${elabArgs.length}, expected ${lf.args.length}", node = node)
            val argMap = lf.args.zip(elabArgs).toMap
            Some(SubstitutionHelper.replacesFree(lf.e)({case (v: Variable) => argMap.get(v) case _ => None }).asInstanceOf[Term])
          case None =>
            KaisarProof.getAt(f) match {
              case Some((trm, lr)) =>
                Some(KaisarProof.makeAt(elaborateFunctions(trm, node), LabelRef(lr.label, lr.args.map(x => elaborateFunctions(x, node)))))
              case None =>
                if (KaisarProof.isBuiltinFunction(f.func)) {
                  val elabChild = elaborateFunctions(f.child, node)
                  Some(FuncOf(f.func, elabChild))
                } else
                  throw ElaborationException(s"Unknown function ${f.func}", node = node)
            }
        }
      case _ => None
    }
  }

  private def replacePreds(t: Formula, node: ASTNode = Triv()): Option[Formula] = {
    t match {
      case f: PredicationalOf =>
        KaisarProof.getAt(f, node) match {
          case Some((trm, lr)) =>
            Some(KaisarProof.makeAt(elaborateFunctions(trm, node), LabelRef(lr.label, lr.args.map(x => elaborateFunctions(x, node)))))
          case None =>
            throw ElaborationException(s"Predicational functions ${f.func} should only be used for internal data structures", node = node)
        }
      case f: PredOf =>
        signature.get(f.func) match {
          case Some(lf) =>
            val elabChild = elaborateFunctions(f.child, node)
            val elabArgs = StandardLibrary.tupleToTerms(elabChild, node)
            if (elabArgs.length != lf.args.length)
              throw ElaborationException(s"Predicate ${f.func.name} called with ${elabArgs.length}, expected ${lf.args.length}", node = node)
            val argMap = lf.args.zip(elabArgs).toMap
            val elabBody = elaborateFunctions(lf.e, node)
            Some(SubstitutionHelper.replacesFree(elabBody)({ case (v: Variable) => argMap.get(v) case _ => None }).asInstanceOf[Formula])
          case None =>
            if (KaisarProof.isBuiltinFunction(f.func)) {
              val elabChild = elaborateFunctions(f.child, node)
              Some(PredOf(f.func, elabChild))
            } else
              throw ElaborationException(s"Unknown predicate function ${f.func}", node = node)
        }
      case _ => None
    }
  }

  def elabFunctionETF(node: ASTNode): ExpressionTraversalFunction = new ExpressionTraversalFunction {
    // note: preorder traversal ensures that when processing  at(x,label()), we see "at(x, label())" first and replace it,
    // rather than seeing just "label()" and getting confused
    override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], IdentPat] =
      replaceFunctions(e, node) match {
        case Some(f) => Right(f)
        case None => Left(None)
      }
    override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] =
      replacePreds(e, node) match {
        case Some(f) => Right(f)
        case None => Left(None)
      }
  }

  /** Elaborate user-defined functions in an expression*/
  def elaborateFunctions(f: Term, node: ASTNode): Term = ExpressionTraversal.traverse(elabFunctionETF(node), f).getOrElse(f)
  def elaborateFunctions(fml: Formula, node: ASTNode): Formula = ExpressionTraversal.traverse(elabFunctionETF(node), fml).getOrElse(fml)
  def elaborateFunctions(e: Expression, node: ASTNode): Expression = e match {case f: Term => elaborateFunctions(f, node) case fml: Formula => elaborateFunctions(fml, node)}


  /** Does the context contain a fact named [[id]]? */
  def contains(id: Ident): Boolean = get(id).isDefined

  /** return all facts that unify with a given pattern */
  def unifyAll(pat: Expression): ContextResult = {
    searchAll(QUnify(pat), Set())
  }
  /** Return first fact that unifies with a pattern, if any. */
  def unify(pat: Expression): Option[(Option[Ident], Formula)] = unifyAll(pat).asList.headOption

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

  val unnamedVar: BaseVariable = BaseVariable("unnamedVar")

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
  private def matchAssume(e: Expression, f: Formula, node: ASTNode = Triv()): ContextResult = {
    e match {
      // [[Nothing]] represents an assumption with no left-hand side, which cannot be referenced by name, but can be searched by program-vars.
      case Nothing => RSuccess(Set((Some(unnamedVar), f)))
      case BaseVariable(x, _, _) => RSuccess(Set((Some(Variable(x)), f)))
      case p: Pair =>
        val bindings = StandardLibrary.factBindings(e, f)
        RSuccess(bindings.toSet, Set())
      case _ =>
        // @TODO: Allows matching arbitrary patterns - delete this feature?
        if (!sameHead(e, f))
          throw ProofCheckException(s"Pattern $e does not match formula $f", node = node)
        (e, f) match {
          case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
            matchAssume(bcf1.left, bcf2.left, node).++(matchAssume(bcf1.right, bcf2.right, node))
          case (ucf1: BinaryCompositeFormula, ucf2: BinaryCompositeFormula) =>
            matchAssume(ucf1.left, ucf2.left, node)
          case (q1: Quantified, q2: Quantified) => matchAssume(q1.child, q2.child, node)
          case (m1: Modal, m2: Modal) => matchAssume(m1.child, m2.child, node)
        }
    }
  }

  // Rename formula according to assignment from an SSA Phi node
  def substPhi(phi: Phi, fml: Formula): Formula = {
    val mapping = phi.reverseMap
    SubstitutionHelper.replacesFree(fml)(term => {
      (KaisarProof.getStable(term), term) match {
        case (Some(_), _) => Some(term)
        case (None, v: Variable) => mapping.get(v)
        case (None, _) => None
      }})}
}