package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics.toSingleFormula
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger.LogConfig
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.language.postfixOps
import scala.math.Ordering.Implicits._
import scala.collection.immutable._

/**
 * Implementation: Tactics that execute and use the output of tools.
 * Also contains tactics for pre-processing sequents.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
private object ToolTactics {

  /** Performs QE and fails if the goal isn't closed. */
  def fullQE(order: List[NamedSymbol] = Nil)(qeTool: => QETool): BelleExpr = {
    Idioms.NamedTactic("QE",
      QELogger.getLogTactic &
      (done | //@note don't fail QE if already proved
        ((alphaRule*) &
        (close |
          ((EqualityTactics.atomExhaustiveEqL2R('L)*) &
          hidePredicates &
          toSingleFormula & assertT(_.succ.head.isFOL, "QE on FOL only") &
            FOQuantifierTactics.universalClosure(order)(1) & rcf(qeTool) &
            (done | ("ANON" by ((s: Sequent) =>
              if (s.succ.head == False) label("QE CEX")
              else DebuggingTactics.done("QE was unable to prove: invalid formula")))
              )
            )
          )
        )
      )
  )}
  def fullQE(qeTool: => QETool): BelleExpr = fullQE()(qeTool)

  // Follows heuristic in C.W. Brown. Companion to the tutorial: Cylindrical algebraic decomposition, (ISSAC 2004)
  // www.usna.edu/Users/cs/wcbrown/research/ISSAC04/handout.pdf
  //For each variable, we need to compute:
  // 1) max degree of variable in the sequent
  // 2) max total-degree of terms containing that variable
  // 3) number of terms containing that variable
  // "Terms" ~= "monomials"
  // This isn't accurate for divisions (which is treated as a multiplication)
  // Map[String,(Int,Int,Int)]
  private def addy(p1:(Int,Int)=>Int,p2:(Int,Int)=>Int,p3:(Int,Int)=>Int,l:(Int,Int,Int),r:(Int,Int,Int)) : (Int,Int,Int) = {
    (p1(l._1,r._1), p2(l._2,r._2), p3(l._3,r._3) )
  }

  private def merge(m1:Map[Variable,(Int,Int,Int)],m2:Map[Variable,(Int,Int,Int)],p1:(Int,Int)=>Int,p2:(Int,Int)=>Int,p3:(Int,Int)=>Int) : Map[Variable,(Int,Int,Int)] = {
    val matches = m1.keySet.intersect(m2.keySet)
    val updm1 = matches.foldLeft(m1)( (m,s) => m+(s->addy(p1,p2,p3,m1(s),m2(s))))
    updm1 ++ (m2 -- m1.keySet)
  }

  private def termDegs(t:Term) : Map[Variable,(Int,Int,Int)] = {

    t match {
      case v:Variable => Map((v,(1,1,1)))
      case Neg(tt) => termDegs(tt)
      case Plus(l,r) => merge( termDegs(l),termDegs(r),(x,y)=>math.max(x,y),(x,y)=>math.max(x,y),(x,y)=>x+y)
      case Minus(l,r) => termDegs(Plus(l,r))
      case Times(l,r) =>
        val lm = termDegs(l)
        val lmax = lm.values.map(p=>p._2).foldLeft(0)((l,r)=>math.max(l,r))
        val rm = termDegs(r)
        val rmax = rm.values.map(p=>p._2).foldLeft(0)((l,r)=>math.max(l,r))
        val lmap = lm.mapValues(p=>(p._1,p._2+rmax,p._3) )
        val rmap = rm.mapValues(p=>(p._1,p._2+lmax,p._3) ) //Updated max term degrees
        merge(lmap,rmap,(x,y)=>x+y,(x,y)=>math.max(x,y),(x,y)=>x+y) /* The 3rd one probably isn't correct for something like x*x*x */
      case Divide(l,r) => termDegs(Times(l,r))
      case Power(p,n:Number) =>
        val pm = termDegs(p)
        //Assume integer powers
        pm.mapValues( (p:(Int,Int,Int)) => (p._1*n.value.toInt,p._2*n.value.toInt,p._3) )
      case FuncOf(_,tt) => termDegs(tt)
      case Pair(l,r) => merge(termDegs(l),termDegs(r),(x,y)=>math.max(x,y),(x,y)=>math.max(x,y),(x,y)=>x+y)
      case _ => Map[Variable,(Int,Int,Int)]()
    }
  }

  //This just takes the max or sum where appropriate
  private def fmlDegs(f:Formula) : Map[Variable,(Int,Int,Int)] = {
    f match {
      case b:BinaryCompositeFormula => merge(fmlDegs(b.left),fmlDegs(b.right),(x,y)=>math.max(x,y),(x,y)=>math.max(x,y),(x,y)=>x+y)
      case u:UnaryCompositeFormula => fmlDegs(u.child)
      case f:ComparisonFormula => merge(termDegs(f.left),termDegs(f.right),(x,y)=>math.max(x,y),(x,y)=>math.max(x,y),(x,y)=>x+y)
      case q:Quantified => fmlDegs(q.child) -- q.vars
      case m:Modal => fmlDegs(m.child) //QE wouldn't understand this anyway...
      case _ => Map() //todo: pred symbols?
    }
  }

  private def seqDegs(s:Sequent) : Map[Variable,(Int,Int,Int)] = {
    (s.ante++s.succ).foldLeft(Map[Variable,(Int,Int,Int)]())(
      (m:Map[Variable,(Int,Int,Int)],f:Formula) => merge(m,fmlDegs(f),(x,y)=>math.max(x,y),(x,y)=>math.max(x,y),(x,y)=>x+y))
  }

  private def equalityOrder[T] : Ordering[T] = new Ordering[T] {
    def compare(x:T,y:T): Int =  0
  }

  private def orderHeuristic(s:Sequent,po:Ordering[Variable]) : List[Variable] = {
    val m = seqDegs(s)
    val ls = m.keySet.toList.sortWith( (x,y) => {
      val c = po.compare(x,y)
      if (c==0) m(x) < m(y)
      else c < 0
      }
    )
    ls
  }

  private def orderedClosure(po:Ordering[Variable]) = new SingleGoalDependentTactic("ordered closure") {
    override def computeExpr(seq: Sequent): BelleExpr = {
      val order = orderHeuristic(seq,po)
      FOQuantifierTactics.universalClosure(order)(1)
    }
  }

  //Note: the same as fullQE except it uses computes the heuristic order in the middle
  def heuristicQE(qeTool: => QETool, po: Ordering[Variable]=equalityOrder): BelleExpr = {
    require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    Idioms.NamedTactic("ordered QE",
      //      DebuggingTactics.recordQECall() &
      done | //@note don't fail QE if already proved
        ((alphaRule*) &
        (close |
          ((EqualityTactics.atomExhaustiveEqL2R('L)*) &
          hidePredicates &
          toSingleFormula & orderedClosure(po) & rcf(qeTool) &
            (done | ("ANON" by ((s: Sequent) =>
              if (s.succ.head == False) label("QE CEX")
              else DebuggingTactics.done("QE was unable to prove: invalid formula")))
              ))))
    )}

  /** Performs QE and allows the goal to be reduced to something that isn't necessarily true.
    * @note You probably want to use fullQE most of the time, because partialQE will destroy the structure of the sequent
    */
  def partialQE(qeTool: => QETool): BelleExpr = {
    require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    Idioms.NamedTactic("pQE",
      toSingleFormula & rcf(qeTool)
    )
  }

  /** Performs Quantifier Elimination on a provable containing a single formula with a single succedent. */
  def rcf(qeTool: => QETool): BelleExpr = "rcf" by ((sequent: Sequent) => {
    require(qeTool != null, "No QE tool available. Use parameter 'qeTool' to provide an instance (e.g., use withMathematica in unit tests)")
    assert(sequent.ante.isEmpty && sequent.succ.length == 1, "Provable's subgoal should have only a single succedent.")
    require(sequent.succ.head.isFOL, "QE only on FOL formulas")

    //Run QE and extract the resulting provable and equivalence
    //@todo how about storing the lemma, but also need a way of finding it again
    //@todo for storage purposes, store rcf(lemmaName) so that the proof uses the exact same lemma without
    val qeFact = ProvableSig.proveArithmetic(qeTool, sequent.succ.head).fact
    val Equiv(_, result) = qeFact.conclusion.succ.head

    cutLR(result)(1) & Idioms.<(
      /*use*/ closeT | skip,
      /*show*/ equivifyR(1) & commuteEquivR(1) & by(qeFact) & done
    )
  })

  /** @see [[TactixLibrary.transform()]] */
  def transform(to: Expression): DependentPositionWithAppliedInputTactic = "transform" byWithInput (to, (pos: Position, sequent: Sequent) => {
    require(sequent.sub(pos) match {
      case Some(fml: Formula) => fml.isFOL && to.kind == fml.kind
      case Some(t: Term) => to.kind == t.kind
      case _ => false
    }, "transform only on arithmetic formulas and terms")

    to match {
      case f: Formula => transformFormula(f, sequent, pos)
      case t: Term => transformTerm(t, sequent, pos)
    }
  })

  /** @see [[TactixLibrary.edit()]] */
  def edit(to: Expression): DependentPositionWithAppliedInputTactic = "edit" byWithInput (to, (pos: Position, sequent: Sequent) => {
    val srcExpr = sequent.sub(pos).getOrElse(throw new IllegalArgumentException("Edit does not point to a term or formula in the sequent"))

    require(srcExpr match {
      case fml: Formula => fml.isFOL && to.kind == fml.kind
      case t: Term => to.kind == t.kind
      case _ => false
    }, "Edit only on arithmetic formulas and terms")

    var nextAbbrvName: Variable = TacticHelper.freshNamedSymbol(Variable("abbrv"), sequent)
    val abbrvs = scala.collection.mutable.Map[PosInExpr, Term]()
    val abbrvTo: Expression =
      //@todo support traverse expressions
      if (to.kind == FormulaKind) ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
          case FuncOf(Function("abbrv", None, _, _, _), abbrv@Pair(_, v: Variable)) =>
            abbrvs(p) = abbrv
            Right(v)
          case FuncOf(Function("abbrv", None, _, _, _), t) =>
            val abbrv = nextAbbrvName
            nextAbbrvName = Variable(abbrv.name, Some(abbrv.index.getOrElse(-1) + 1))
            abbrvs(p) = Pair(t, abbrv)
            Right(abbrv)
          case _ => Left(None)
        }
      }, to.asInstanceOf[Formula]).get
      else ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
          case FuncOf(Function("abbrv", None, _, _, _), abbrv@Pair(_, v: Variable)) =>
            abbrvs(p) = abbrv
            Right(v)
          case FuncOf(Function("abbrv", None, _, _, _), t) =>
            val abbrv = nextAbbrvName
            nextAbbrvName = Variable(abbrv.name, Some(abbrv.index.getOrElse(-1) + 1))
            abbrvs(p) = Pair(t, abbrv)
            Right(abbrv)
          case _ => Left(None)
        }
      }, to.asInstanceOf[Term]).get
    //@todo unify to check whether abbrv is valid; may need reassociating, e.g. in x*y*z x*abbrv(y*z)

    val abbrvTactic = abbrvs.values.map({
      case Pair(t, v: Variable) => EqualityTactics.abbrv(t, Some(v))
    }).reduceOption[BelleExpr](_&_).getOrElse(skip)

    abbrvTactic & transform(abbrvTo)(pos)
  })

  /** Transforms the formula at position `pos` into the formula `to`. */
  private def transformFormula(to: Formula, sequent: Sequent, pos: Position) = {
    val polarity = FormulaTools.polarityAt(sequent(pos.top), pos.inExpr)*(if (pos.isSucc) 1 else -1)

    val (src, tgt) = (sequent.sub(pos), to) match {
      case (Some(src: Formula), tgt: Formula) => if (polarity > 0) (tgt, src) else (src, tgt)
    }

    val boundVars = StaticSemantics.boundVars(sequent(pos.top))
    val gaFull = if (pos.isSucc) sequent.ante.flatMap(FormulaTools.conjuncts) else sequent.ante.patch(pos.top.getIndex, Nil, 1).flatMap(FormulaTools.conjuncts)

    def proveFact(assumptions: IndexedSeq[Formula], filters: List[IndexedSeq[Formula]=>IndexedSeq[Formula]]): (ProvableSig, IndexedSeq[Formula]) = {
      val filteredAssumptions = filters.head(assumptions)
      lazy val filteredAssumptionsFml = filteredAssumptions.reduceOption(And).getOrElse(True)
      val pr =
        if (filteredAssumptions.isEmpty) proveBy(Imply(src, tgt), master())
        else if (polarity > 0) proveBy(Imply(And(filteredAssumptionsFml, src), tgt), master())
        else proveBy(Imply(filteredAssumptionsFml, Imply(src, tgt)), master())

      if (pr.isProved || filters.tail.isEmpty) (pr, filteredAssumptions)
      else proveFact(assumptions, filters.tail)
    }
    //@note first try to prove without assumptions, than with non-bound stuff, if all that fails with whole ante
    val (fact, ga) = proveFact(gaFull,
      ((al: IndexedSeq[Formula]) => al.filter(_ => false))::
        ((al: IndexedSeq[Formula]) => al.filter(fml => StaticSemantics.freeVars(fml).intersect(boundVars).isEmpty))::
        ((al: IndexedSeq[Formula]) => al.filter(_ => true))::Nil)

    def propPushLeftIn(op: (Formula, Formula) => Formula) = {
      val p = "p_()".asFormula
      val q = "q_()".asFormula
      val r = "r_()".asFormula
      proveBy(Imply(op(p, Imply(q, r)), Imply(op(p, q), op(p, r))), prop & done)
    }

    def propPushRightIn(op: (Formula, Formula) => Formula) = {
      val p = "p_()".asFormula
      val q = "q_()".asFormula
      val r = "r_()".asFormula
      proveBy(Imply(op(Imply(q, r), p), Imply(op(q, p), op(r, p))), prop & done)
    }

    lazy val implyFact = proveBy("q_() -> (p_() -> p_()&q_())".asFormula, prop & done)
    lazy val existsDistribute = proveBy("(\\forall x_ (p(x_)->q(x_))) -> ((\\exists x_ p(x_))->(\\exists x_ q(x_)))".asFormula,
      implyR(1) & implyR(1) & existsL(-2) & allL(-1) & existsR(1) & prop & done)

    def pushIn(remainder: PosInExpr): DependentPositionTactic = "ANON" by ((pp: Position, ss: Sequent) => (ss.sub(pp) match {
      case Some(Imply(left: BinaryCompositeFormula, right: BinaryCompositeFormula)) if left.getClass==right.getClass && left.left==right.left =>
        useAt(propPushLeftIn(left.reapply), PosInExpr(1::Nil))(pp)
      case Some(Imply(left: BinaryCompositeFormula, right: BinaryCompositeFormula)) if left.getClass==right.getClass && left.right ==right.right =>
        useAt(propPushRightIn(left.reapply), PosInExpr(1::Nil))(pp)
      case Some(Imply(Box(a, _), Box(b, _))) if a==b => useAt("K modal modus ponens", PosInExpr(1::Nil))(pp)
      case Some(Imply(Forall(lv, _), Forall(rv, _))) if lv==rv => useAt(DerivedAxioms.allDistributeAxiom, PosInExpr(1::Nil))(pp)
      case Some(Imply(Exists(lv, _), Exists(rv, _))) if lv==rv => useAt(existsDistribute, PosInExpr(1::Nil))(pp)
      case Some(Imply(_, _)) => useAt(implyFact, PosInExpr(1::Nil))(pos)
      case Some(_) => skip
    }) & (if (remainder.pos.isEmpty) skip else pushIn(remainder.child)(pp ++ PosInExpr(remainder.head::Nil))))

    val key = if (polarity > 0) PosInExpr(1::Nil) else if (ga.isEmpty) PosInExpr(0::Nil) else PosInExpr(1::0::Nil)

    if (fact.isProved && ga.isEmpty) useAt(fact, key)(pos)
    else if (fact.isProved && ga.nonEmpty) useAt(fact, key)(pos) & (
      if (polarity < 0) Idioms.<(skip, master())
      else cutAt(ga.reduce(And))(pos) & Idioms.<(
        //@todo ensureAt only closes branch when original conjecture is true
        ensureAt(pos) & OnAll(master() & done),
        pushIn(pos.inExpr)(pos.top)
      )
      )
    else throw BelleTacticFailure(s"Invalid transformation: $to")
  }

  /** Transforms the term at position `pos` into the term `to`. */
  private def transformTerm(to: Term, sequent: Sequent, pos: Position) = {
    val src = sequent.sub(pos) match { case Some(src: Term) => src }
    useAt(proveBy(Equal(src, to), QE & done), PosInExpr(0::Nil))(pos)
  }

  /** Ensures that the formula at position `pos` is available at that position from the assumptions. */
  private def ensureAt: DependentPositionTactic = "ANON" by ((pos: Position, seq: Sequent) => {
    lazy val ensuredFormula = seq.sub(pos) match { case Some(fml: Formula) => fml }
    lazy val ensuredFree = StaticSemantics.freeVars(ensuredFormula).toSet
    lazy val skipAt = "ANON" by ((_: Position, _: Sequent) => skip)

    lazy val step = seq(pos.top) match {
      case Box(ODESystem(_, _), _) => diffInvariant(ensuredFormula)(pos.top) & dW(pos.top) & implyR(pos.top)
      case Box(Loop(_), _) => loop(ensuredFormula)(pos.top) & Idioms.<(master(), skip, master())
      case Box(Test(_), _) => testb(pos.top) & implyR(pos.top)
      case Box(_, _) => TactixLibrary.step(pos.top)
      case Forall(v, _) if pos.isAnte =>
        if (ensuredFree.intersect(v.toSet).isEmpty) ??? //@todo instantiate with something useful
        else allL(v.head)(pos.top)
      case Forall(_, _) if pos.isSucc => allR(pos.top)
      case Exists(v, _) if pos.isSucc =>
        if (ensuredFree.intersect(v.toSet).isEmpty) ???
        else existsR(v.head)(pos.top)
      case Exists(_, _ ) if pos.isAnte => existsL(pos.top)
      //@todo resulting branches may not be provable when starting from wrong question, e.g., a>0&b>0 -> x=2 & a/b>0, even if locally a>0&b>0 -> (a/b>0 <-> a>0*b)
      case e if pos.isAnte => TacticIndex.default.tacticsFor(e)._1.headOption.getOrElse(skipAt)(pos.top)
      case e if pos.isSucc => TacticIndex.default.tacticsFor(e)._2.headOption.getOrElse(skipAt)(pos.top)
    }
    val recurse = if (pos.isTopLevel) skip else ensureAt(pos.top.getPos, pos.inExpr.child)
    if (seq.isFOL) QE else step & onAll(recurse)
  })

  /* Hides all predicates (QE cannot handle predicate symbols) */
  private def hidePredicates: DependentTactic = "ANON" by ((sequent: Sequent) =>
    (  sequent.ante.zipWithIndex.filter({ case (_: PredOf, _) => true case _ => false}).reverse.map({ case (fml, i) => hideL(AntePos(i), fml) })
    ++ sequent.succ.zipWithIndex.filter({ case (_: PredOf, _) => true case _ => false}).reverse.map({ case (fml, i) => hideR(SuccPos(i), fml) })
      ).reduceOption[BelleExpr](_ & _).getOrElse(skip)
  )
}
