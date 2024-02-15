/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.util.Random
import scala.collection.immutable
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

/**
 * Random formula generator and random term generator and random program generator
 * for testing purposes.
 * Each use of RandomFormula will print a random seed with which the same random tests can be repeated.
 * {{{
 *   val rand = RandomFormula()
 *   // will print something like RandomFormula(-4317240407825764493L) on screen
 *   // The same sequence of pseudo-random formulas can, thus, be regenerated again from
 *   val sameRand = RandomFormula(-4317240407825764493L)
 * }}}
  *
  * @author Andre Platzer
 * @param seed the random seed, for repeatable random testing purposes.
 */
class RandomFormula(val seed: Long = new Random().nextLong()) {
  println("regenerate by RandomFormula(" + seed + "L)")
  val rand: Random = new Random(seed)
  /** probability of prematurely stopping short at any given operator */
  private val shortProbability = 0.05
  private val randomReps = 500

  private val funcNames = "ff" :: "gg" :: "hh" :: "ii" :: Nil
  private val predNames = "pp" :: "qq" :: "rr" :: "ss" :: Nil
  private val progNames = "aa" :: "bb" :: "cc" :: "dd" :: Nil


  /** next RandomFormula episode */
  def nextFormulaEpisode(): RandomFormula = {print("episode "); new RandomFormula(rand.nextLong())}

  // expression generators

  def nextExpression(size: Int): Expression = rand.nextInt(4) match {
    case 0 => nextTerm(size)
    case 1 => nextFormula(size)
    case 2 => nextProgram(size)
    case 3 => nextDifferentialProgram(size)
  }

  /** randomly generate a term of the given expected size */
  def nextTerm(size : Int): Term = nextT(nextNames("z", size / 3 + 1), size)

  /** randomly generate a formula of the given expected size */
  def nextFormula(size : Int): Formula = nextF(nextNames("z", size / 3 + 1), size)

  /** randomly generate a program/game of the given expected size */
  def nextProgram(size : Int): Program = nextP(nextNames("z", size / 3 + 1), size)

  /** randomly generate a hybrid system without games of the given expected size */
  def nextSystem(size : Int): Program = nextP(nextNames("z", size / 3 + 1), size, dotTs=false, dotFs=false, diffs=true, funcs=false, duals=false)

  /** randomly generate a differential program of the given expected size */
  def nextDifferentialProgram(size : Int): DifferentialProgram = nextDP(nextNames("z", size / 3 + 1), size)


  // dot generators default to no diffs
  def nextDotTerm(size : Int): Term = nextT(nextNames("z", size / 3 + 1), size, dots=true, diffs=false, funcs=false)

  def nextDotFormula(size : Int): Formula = nextF(nextNames("z", size / 3 + 1), size, modals=true, dotTs=true, dotFs=true, diffs=false, funcs=false, duals=isGame)

  def nextDotProgram(size : Int): Program = nextP(nextNames("z", size / 3 + 1), size, dotTs=true, dotFs=false, diffs=false, funcs=false, duals=isGame)

  def nextDotExpression(size: Int): Expression = rand.nextInt(3) match {
    case 0 => nextDotTerm(size)
    case 1 => nextDotFormula(size)
    case 2 => nextDotProgram(size)
  }

  /** randomly generate a formula context C{_} of the given expected size */
  def nextFormulaContext(size : Int): Context[Formula] = {
    import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
    val fml = nextF(nextNames("z", size / 3 + 1), 2*size, modals=true, dotTs=false, dotFs=false, diffs=false, funcs=false, duals=isGame)
    for (j <- 1 to randomReps) {
      //@todo min(size, fml.size)
      val pos = nextPosition(size).inExpr
      try { return fml.at(pos)._1 }
      catch {case _: IllegalArgumentException => }
    }
    throw new IllegalStateException("Monte Carlo generation of context failed despite " + randomReps + " rounds for " + fml)
  }

  def nextSequent(size : Int): Sequent = {
    val vars = nextNames("z", size / 3 + 1)
    Sequent(Range(0,rand.nextInt(size/2)).map(i => nextF(vars, size-1)), Range(0,rand.nextInt(size/2)).map(i => nextF(vars, size-1)))
  }

  /** Generate a random proof of a random tautological sequent */
  def nextProvable(size: Int): ProvableSig = nextPr(nextNames("z", size / 3 + 1), size)

  /** Generate a random schematic instance of the given Formula `fml` of expected complexity `size`.
    * @param renamed whether variables can have been renamed in the schematic instance generated.
    * @param builtins whether built-in names can be used in the schematic instance, or 'false' if fresh.
    * @param diffs whether differentials can be used in the schematic instance. */
  def nextSchematicInstance(fml: Formula, size: Int, renamed: Boolean = true, builtins: Boolean = false, diffs: Boolean = false): Formula = {
    val diffPrgConsts = new ListBuffer[Set[NamedSymbol]]()
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preP(p: PosInExpr, e: Program): Either[Option[ExpressionTraversal.StopTraversal], Program] = e match {
        case ODESystem(ode: DifferentialProduct, _) =>
          val diffconsts = StaticSemantics.signature(ode).filter(_.isInstanceOf[DifferentialProgramConst])
          diffconsts.subsets(1).foreach(diffPrgConsts += _)
          Left(None)
        case _ => Left(None)
      }
    }, fml)

    val signature = StaticSemantics.signature(fml)
    val symbols =
      if (diffPrgConsts.size <= 1) signature.groupBy(_ => 0)
      else signature.groupBy(s => diffPrgConsts.indexWhere(_.contains(s)))

    val ownvars = StaticSemantics.vars(fml).symbols.filter(x => x.isInstanceOf[BaseVariable]).
      filter(x => builtins || !x.name.endsWith("_"))
    // three different piles of variables to avoid accidental capture during the schematic instantiation
    val vars = nextNames("z", size / 3 + 1)
    val odevars = (1 to symbols.partition(_._1 >= 0)._1.size).map(i => nextNames("o" + i, size / 3 + 1))
    val othervars = nextNames("y", size / 5 + 1)

    //@todo make sure not to create diffs when the symbol occurs within another diff
    val repls: Set[(Expression,Expression)] = symbols.map({ case (i, s) => s.map({
      case p@UnitPredicational(_,AnyArg) => if (diffs) p->nextF(vars,size) else p->nextF(vars,size,modals=true, dotTs=false, dotFs=false,diffs=false,funcs=false,duals=isGame)
      case p@UnitPredicational(_,Except(_)) => p->nextF(vars,size,modals=true,dotTs=false, dotFs=false,diffs=false,funcs=false,duals=isGame)
      // need to teach the term some manners such as no diffs if occurs in ODE
      case p@UnitFunctional(_,AnyArg,_) => p->nextT(vars,size,dots=false,diffs=false,funcs=true)
      case p@UnitFunctional(_,Except(_),_) => p->nextT(vars,size,dots=false,diffs=false,funcs=false)
      case a: ProgramConst => a->nextP(vars,size)
      case a: SystemConst => a->nextP(vars,size,dotTs=true, dotFs=true, diffs=diffs, funcs=false, duals=false)
      case a: DifferentialProgramConst => a->nextDP(odevars(i),size)
      case f@Function(_,_,Unit,Real,None) => FuncOf(f,Nothing)->nextT(othervars,size,dots=false,diffs=false,funcs=false)
      case p@Function(_,_,Unit,Bool,None) => PredOf(p,Nothing)->nextF(othervars,size,modals=true, dotTs=false, dotFs=false,diffs=false,funcs=false,duals=isGame)
      case f@Function(_,_,Real,Real,None) => FuncOf(f,DotTerm())->nextT(othervars,size,dots=true,diffs=false,funcs=false)
      case p@Function(_,_,Real,Bool,None) => PredOf(p,DotTerm())->nextF(othervars,size,modals=true, dotTs=true, dotFs=false,diffs=false,funcs=false,duals=isGame)
      //@todo replace also as PredicationalOf
      case ow => ow->ow
    })}).toSet.flatten
    def doRepl(f: Formula, repl: (Expression, Expression)): Formula =
      if (repl._1==repl._2) f else f.replaceAll(repl._1, repl._2)
    println("Replace all " + repls.mkString(", "))
    // do all replacements repl to fml
    val inst = repls.foldRight(fml) ((repl, f) => doRepl(f,repl))
    if (!renamed)
      inst
    else {
      try {
        val instvars = StaticSemantics.vars(inst).symbols
        // random renamings of original ownvars from the axiom to some of allvars, including possibly ownvars again
        // remove variables whose diff symbols occur to prevent accidentally creating duplicate ODEs by renaming
        val allvars: List[Variable] = instvars.filter(x => x.isInstanceOf[BaseVariable] &&
          !instvars.contains(DifferentialSymbol(x.asInstanceOf[BaseVariable]))
        ).toList
        val renamings: immutable.Seq[(Variable, Variable)] = ownvars.map(x => (x.asInstanceOf[BaseVariable].asInstanceOf[Variable],
          (if (rand.nextBoolean() || allvars.isEmpty) x else allvars(rand.nextInt(allvars.length))))).toSeq
        val noncycrenamings = renamings.filter(sp => !renamings.exists(p => p._1 == sp._2))
        val ren = MultiRename(noncycrenamings)
        val renamedInst = ren(inst)
        val other = try {
          ren.toCore(inst)
        } catch {
          // exception can happen when MultiRename used semantic renaming
          case ignore: Throwable => inst
        }
        if (other == renamedInst)
          renamedInst
        else {
          // strangely, both renamings disagree
          println("MultiRename disagrees with toCore renaming: " + ren + "\n of: " + inst)
          throw new IllegalStateException("MultiRename disagrees with toCore renaming: " + ren + "\n of: " + inst)
          // inst
        }
      } catch {
        // for example (x')' disallowed at present
        case ignore: CoreException => if (diffs)
          nextSchematicInstance(fml, size, renamed=renamed, builtins=builtins, diffs=false)
        else
          throw ignore
      }
    }
  }


  /** Generate a random admissible uniform substitution for the given Formula `fml` of expected complexity `size`.
    * @note Tries hard to be admissible but won't always be for all formulas.
    *       It should shift variables on nesting occurrences such as
    *       qq(ff()) for qq(.)~>[u1:=5].>=0, ff()~>2*u1
    * @requires no function/predicate occurrences within Differentials because those might cause inadmissibility if replaced free
    * @param diffs whether differentials can be used in the schematic instance. */
  def nextAdmissibleUSubst(fml: Formula, size: Int, diffs: Boolean = false): USubst = {
    val replacedFuncs = false
    val ownvars: Set[Variable] = StaticSemantics.vars(fml).symbols.filter(x => x.isInstanceOf[BaseVariable])
    // disjoint pile of variables to avoid accidental capture during the schematic instantiation
    val othervars: IndexedSeq[Variable] = (nextNames("u", size / 5 + 1).toSet--ownvars).toIndexedSeq
    val vars = (ownvars++othervars).toIndexedSeq
    val symbols = StaticSemantics.signature(fml)
    //@todo make sure not to create diffs when the symbol occurs within another diff
    val repls: Set[(Expression,Expression)] = symbols.map(sym => sym match {
      case p@UnitPredicational(_,AnyArg) => if (diffs) p->nextF(vars,size, modals=true,dotTs=false,dotFs=false,diffs=false,funcs=false,duals=isGame)
      else p->nextF(vars,size,modals=true, dotTs=false, dotFs=false,diffs=false,funcs=replacedFuncs,duals=isGame)
      case p@UnitPredicational(_,Except(_)) => p->nextF(vars,size,modals=true,dotTs=false, dotFs=false,diffs=false,funcs=replacedFuncs,duals=isGame)
      // need to teach the term some manners such as no diffs if occurs in ODE
      case p@UnitFunctional(_,AnyArg,_) => p->nextT(vars,size,dots=false,diffs=false,funcs=replacedFuncs)
      case p@UnitFunctional(_,Except(_),_) => p->nextT(vars,size,dots=false,diffs=false,funcs=replacedFuncs)
      case a: ProgramConst => a->nextP(vars,size)
      case a: SystemConst => a->nextP(vars,size,dotTs=true, dotFs=true, diffs=diffs, funcs=replacedFuncs, duals=false)
      case a: DifferentialProgramConst => a->nextDP(vars,size)
      case f@Function(_,_,Unit,Real,None) => FuncOf(f,Nothing)->nextT(othervars,size,dots=false,diffs=false,funcs=replacedFuncs)
      case p@Function(_,_,Unit,Bool,None) => PredOf(p,Nothing)->nextF(othervars,size,modals=true, dotTs=false, dotFs=false,diffs=false,funcs=replacedFuncs,duals=isGame)
      case f@Function(_,_,Real,Real,None) => FuncOf(f,DotTerm())->nextT(othervars,size,dots=true,diffs=false,funcs=replacedFuncs)
      case p@Function(_,_,Real,Bool,None) => PredOf(p,DotTerm())->nextF(othervars,size,modals=true, dotTs=true, dotFs=false,diffs=false,funcs=replacedFuncs,duals=isGame)
      case p@Function(_,_,Bool,Bool,None) => PredicationalOf(p,DotFormula)->nextF(othervars,size,modals=true, dotTs=false,dotFs=true,diffs=false,funcs=replacedFuncs,duals=isGame)
      case ow => ow->ow
    })
    USubst(repls.filter(pair=>pair._1!=pair._2).map(pair=>SubstitutionPair(pair._1,pair._2)).toSeq)
  }


    /** Generate a random (propositionally) provable formula */
  //def nextProved(size: Int): Sequent = nextProvable(size).conclusion

  /** weaken p1 and p2 such that they have the same context except at position `pos` */
  private def weakenRight(p1: ProvableSig, p2: ProvableSig, pos: SuccPos): (ProvableSig,ProvableSig) = {
    require(pos.getIndex==0, "currently only implemented for first succedent position")
    ???
  }

  /** Apply Rule Forward: like Provable.apply(Sequent,Rule) except for two premises */
  private def prolong(p1: ProvableSig, p2: ProvableSig, newConsequence: Sequent, rule: Rule): ProvableSig = {
    ProvableSig.startPlainProof(newConsequence)(rule, 0)(p1, 0)(p2, 1)
  }

  /** padding such that at least lefts many formula in antecedent of pr by weakening */
  @tailrec
  private def padLeft(vars : IndexedSeq[Variable], n : Int, pr: ProvableSig, lefts: Int): ProvableSig = {
    require(lefts>=0)
    if (pr.conclusion.ante.length >= lefts) pr
    else {
      val fml = nextF(vars, n)
      padLeft(vars, n, pr(pr.conclusion.glue(Sequent(IndexedSeq(fml), IndexedSeq())), HideLeft(AntePos(pr.conclusion.ante.length))), lefts)
    }
  }

  /** padding such that at least rights many formula in succedent of pr by weakening */
  @tailrec
  private def padRight(vars : IndexedSeq[Variable], n : Int, pr: ProvableSig, rights: Int): ProvableSig = {
    require(rights>=0)
    if (pr.conclusion.succ.length >= rights) pr
    else {
      val fml = nextF(vars, n)
      padRight(vars, n, pr(pr.conclusion.glue(Sequent(IndexedSeq(), IndexedSeq(fml))), HideRight(SuccPos(pr.conclusion.succ.length))), rights)
    }
  }

  /** Randomly generate a PosInExpr that is defined and of the expected kind in the given expression.
    * @param kind What kind of subexpressions to collect.
    *             `ExpressionKind` means any subterm/subformula/subprogram/...
    * @ensures e.at(\result).isDefined && e.at(\result).get.kind==kind */
  def nextSubPosition(e: Expression, kind: Kind): PosInExpr = {
    val l: List[(Kind, PosInExpr)] = Augmentors.ExpressionAugmentor(e).listSubPos.
      filter(k => kind==ExpressionKind || k._1==kind)
    l(rand.nextInt(l.length))._2
  }

  /** Randomly generate a top-level SeqPos that is defined in the given sequent.
    * @ensures seq(\result) throws no Exception */
  def nextSeqPos(seq: Sequent): SeqPos = {
    if (seq.ante.isEmpty && seq.succ.isEmpty)
        throw new IllegalArgumentException("No defined positions in empty sequent")
    val ant = if (seq.ante.isEmpty) false else if (seq.succ.isEmpty) true else rand.nextBoolean()
    if (ant)
      SeqPos(-1 - rand.nextInt(seq.ante.length))
    else
      SeqPos(1 + rand.nextInt(seq.succ.length))
  }


  // closer to implementation-specific

  /** Randomly generate some arbitrary position */
  def nextPosition(size : Int): Position = if (rand.nextBoolean())
    AntePosition.base0(rand.nextInt(size), PosInExpr(nextPos(size)))
  else
    SuccPosition.base0(rand.nextInt(size), PosInExpr(nextPos(size)))

  def unfoldRight[A, B](seed: B)(f: B => Option[(A,B)]): List[A] = f(seed) match {
    case Some((a,b)) => a :: unfoldRight(b)(f)
    case None => Nil
  }
  
  def nextNames(name: String, n : Int) : IndexedSeq[Variable] = unfoldRight(n) { n =>
    if (n==0)
      None
    else
      Some((Variable(name + n, None, Real), n-1))
      //Some(("x" + (rand.alphanumeric take 5).fold("")((s:String,t:String)=>s+t), n-1))
  }.toIndexedSeq

  private def nextPos(n : Int) : List[Int] = {
    require(n >= 0)
    if (n == 0 || rand.nextFloat()<=shortProbability) return Nil
    (if (rand.nextBoolean()) 1 else 0) :: nextPos(n - 1)
  }

  // configurable random generator implementations

  def nextT(vars : IndexedSeq[Variable], n : Int) : Term = nextT(vars, n, dots=false, diffs=true, funcs=true)
  def nextT(vars : IndexedSeq[Variable], n : Int, dots: Boolean) : Term = nextT(vars, n, dots=dots, diffs= !dots, funcs=true)

  def nextT(vars : IndexedSeq[Variable], n : Int, dots: Boolean, diffs: Boolean, funcs: Boolean) : Term = {
    require(n>=0)
    if (n == 0 || rand.nextFloat()<=shortProbability) return if (dots && rand.nextInt(100)>=50) {assert(dots); DotTerm()} else Number(BigDecimal(1))
    val r = rand.nextInt(if (dots) 110 else 95/*+1*/)
    r match {
      case 0 => Number(BigDecimal(0))
        //@todo directly generate negative numbers too?
      case it if 1 until 10 contains it => if (rand.nextBoolean()) Number(BigDecimal(rand.nextInt(100))) else Number(BigDecimal(-rand.nextInt(100)))
      case it if 10 until 20 contains it => vars(rand.nextInt(vars.length))
      case it if 20 until 30 contains it => Plus(nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs))
      case it if 30 until 40 contains it => Minus(nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs))
      case it if 40 until 50 contains it => Times(nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs))
      case it if 50 until 55 contains it => val dividend = nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs); val divisor = nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs)
        //@todo avoid zero division better by checking for evaluation to zero as in x/(0+0)
        if (divisor==Number(0)) Divide(dividend, Number(1)) else Divide(dividend, divisor)
        //@todo avoid 0^0
      case it if 55 until 60 contains it => Power(nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs), Number(BigDecimal(rand.nextInt(6))))
      case it if (60 until 70 contains it) && diffs => DifferentialSymbol(vars(rand.nextInt(vars.length)))
      case it if (70 until 80 contains it) && diffs => nextT(vars, n-1, dots=dots, diffs=false, funcs=funcs) match {
        case n: Number => n
        case t => Differential(t)
      }
      case it if (80 until 84 contains it) && funcs => FuncOf(Function(funcNames(rand.nextInt(funcNames.length))+ "0",None,Unit,Real),Nothing)
      case it if (84 until 88 contains it) && funcs => FuncOf(Function(funcNames(rand.nextInt(funcNames.length)),None,Real,Real), nextT(vars, n-1, dots=dots,diffs=diffs,funcs=funcs))
      case it if (88 until 95 contains it) && funcs => UnitFunctional(funcNames(rand.nextInt(funcNames.length)).toUpperCase,AnyArg,Real)
      case it if 95 until 200 contains it => assert(dots); DotTerm()
      // cleanup case without diffs and funcs emphasizes nonzero constants and variables to make for more interesting polynomials etc.
      case it if (60 until 200 contains it) && (!diffs || !funcs) =>
        if (r%2==0) vars(rand.nextInt(vars.length)) else Number(BigDecimal(1+rand.nextInt(100)))
      case _ => throw new IllegalStateException("random number generator range for term generation produces the right range " + r)
    }
  }


  def nextF(vars : IndexedSeq[Variable], n : Int) : Formula = nextF(vars, n, modals=true, dotTs=false, dotFs=false)
  def nextF(vars : IndexedSeq[Variable], n : Int, modals: Boolean, dotTs: Boolean, dotFs: Boolean) : Formula = nextF(vars, n, modals=modals, dotTs=dotTs, dotFs=dotFs, diffs= !(dotTs||dotFs), funcs=dotTs&&dotFs)
  def nextF(vars : IndexedSeq[Variable], n : Int, modals: Boolean, dotTs: Boolean, dotFs: Boolean, diffs: Boolean, funcs: Boolean) : Formula = nextF(vars, n, modals=modals, dotTs=dotTs, dotFs=dotFs, diffs, funcs, duals=isGame)
  def nextF(vars : IndexedSeq[Variable], n : Int, modals: Boolean, dotTs: Boolean, dotFs: Boolean, diffs: Boolean, funcs: Boolean, duals: Boolean) : Formula = {
	  require(n>=0)
	  if (n == 0 || rand.nextFloat()<=shortProbability) return if (dotFs && rand.nextInt(100)>=70) {assert(dotFs);DotFormula} else True
      val r = rand.nextInt(if (dotFs) 380 else 340)
      r match {
        case 0 => False
        case 1 => True
        case it if 2 until 10 contains it => Equal(nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case it if 10 until 20 contains it => Not(nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 20 until 30 contains it => And(nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 30 until 40 contains it => Or(nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 40 until 50 contains it => Imply(nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 50 until 60 contains it => Equiv(nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 60 until 70 contains it => NotEqual(nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case it if 70 until 80 contains it => GreaterEqual(nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case it if 80 until 90 contains it => LessEqual(nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case it if 90 until 100 contains it => Greater(nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case it if 100 until 110 contains it => Less(nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case it if 110 until 140 contains it => Forall(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 140 until 170 contains it => Exists(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 170 until 230 contains it => Box(nextP(vars, n-1, dotTs, dotFs, diffs, funcs,duals=duals), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if 230 until 290 contains it => Diamond(nextP(vars, n-1, dotTs, dotFs, diffs, funcs,duals=duals), nextF(vars, n-1, modals=modals,dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
        case it if (290 until 300 contains it) && diffs => DifferentialFormula(nextF(vars, n-1, false, false, false, false, false,duals=false))
        case it if (300 until 310 contains it) && funcs => PredOf(Function(predNames(rand.nextInt(predNames.length))+ "0",None,Unit,Bool),Nothing)
        case it if (310 until 320 contains it) && funcs => PredOf(Function(predNames(rand.nextInt(predNames.length)),None,Real,Bool), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case it if (320 until 330 contains it) && funcs => PredicationalOf(Function(predNames(rand.nextInt(predNames.length)).toUpperCase + "1",None,Bool,Bool), nextF(vars, n-1, modals, dotTs=false, dotFs=false, diffs=diffs,funcs=funcs,duals=duals))
        case it if (330 until 340 contains it) && funcs => UnitPredicational(predNames(rand.nextInt(predNames.length)).toUpperCase,AnyArg)
        case it if 340 until 400 contains it => assert(dotFs); DotFormula
        case it if (0 to 400 contains it) && (!diffs || !funcs) => GreaterEqual(nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
        case _ => throw new IllegalStateException("random number generator range for formula generation produces the right range " + r)
      }
  }

  /** whether games are currently allowed */
  private[this] val isGame: Boolean = try {Dual(AssignAny(Variable("x"))); true} catch {case ignore: IllegalArgumentException => false }

  def nextP(vars : IndexedSeq[Variable], n : Int) : Program = nextP(vars, n, dotTs=false, dotFs=false)
  def nextP(vars : IndexedSeq[Variable], n : Int, dotTs: Boolean, dotFs: Boolean) : Program = nextP(vars, n, dotTs=dotTs, dotFs=dotFs, diffs= !(dotTs || dotFs), funcs=dotTs&&dotFs, duals=isGame)
  def nextP(vars : IndexedSeq[Variable], n : Int, dotTs: Boolean, dotFs: Boolean, diffs: Boolean, funcs: Boolean, duals: Boolean) : Program = {
    require(n>=0)
    if (n == 0 || rand.nextFloat()<=shortProbability) return Test(True)
    val r = rand.nextInt(200)
    r match {
      case 0 => Test(False)
      case 1 => Test(True)
      case it if 2 until 10 contains it => val v = vars(rand.nextInt(vars.length)); Assign(v, v)
      case it if 10 until 20 contains it => Test(nextF(vars, n-1, true, dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
      case it if 20 until 30 contains it => Assign(vars(rand.nextInt(vars.length)), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
      case it if (30 until 35 contains it) && diffs => Assign(DifferentialSymbol(vars(rand.nextInt(vars.length))), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
      case it if 35 until 40 contains it => AssignAny(vars(rand.nextInt(vars.length)))
      case it if (40 until 50 contains it) && diffs => ODESystem(nextDP(vars, n, dotTs=dotTs, funcs=funcs), nextF(vars, n-1, true, dotTs=dotTs,dotFs=dotFs,diffs=false,funcs=funcs,duals=duals))
      case it if 50 until 100 contains it => Choice(nextP(vars, n-1, dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals), nextP(vars, n-1, dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
      case it if 100 until 150 contains it => Compose(nextP(vars, n-1, dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals), nextP(vars, n-1, dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
      case it if (190 until 220 contains it) && duals => Dual(nextP(vars, n-1, dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
      case it if 150 until 190 contains it => Loop(nextP(vars, n-1, dotTs=dotTs,dotFs=dotFs,diffs=diffs,funcs=funcs,duals=duals))
      case it if (190 until 200 contains it) && funcs => ProgramConst(progNames(rand.nextInt(progNames.length)))
      case it if (1 until 200 contains it) && (!diffs || !funcs) => Assign(vars(rand.nextInt(vars.length)), nextT(vars, n-1, dots=dotTs,diffs=diffs,funcs=funcs))
      case _ => throw new IllegalStateException("random number generator range for program generation produces the right range " + r)
    }
  }

  private def nextDP(vars: IndexedSeq[Variable], n: Int): DifferentialProgram = nextDP(vars, n, dotTs=false, funcs=false)
  private def nextDP(vars: IndexedSeq[Variable], n: Int, dotTs: Boolean, funcs: Boolean): DifferentialProgram =
    nextODE(vars, n, 0, vars.length, dotTs=dotTs, funcs=funcs)

  /**
   * randomly generate an ODE paying attention to avoid duplicates.
   * This algorithm is merg-sort-esque and only generates ODEs for differential equations of
   * vars[lower..upper)
   * It just watches that both subintervals remain nonempty
   */
  private def nextODE(vars : IndexedSeq[Variable], n : Int, lower: Int, upper: Int, dotTs: Boolean, funcs: Boolean) : DifferentialProgram = {
    require(n>=0)
    require(0<=lower && lower<upper && upper<=vars.length)
    if (lower == upper-1) return AtomicODE(DifferentialSymbol(vars(lower)), nextT(vars, 0, dots=dotTs, diffs=false, funcs=funcs))
    val v = lower + rand.nextInt(upper-lower)
    assert(lower <= v && v < upper)
    if (n == 0 || rand.nextFloat()<=shortProbability
      || lower==v || v == upper-1) return AtomicODE(DifferentialSymbol(vars(v)), nextT(vars, 0, dots=dotTs, diffs=false, funcs=funcs))
    val r = rand.nextInt(20)
    r match {
      case it if 0 until 10 contains it => AtomicODE(DifferentialSymbol(vars(v)), nextT(vars, n-1, dots=dotTs, diffs=false, funcs=funcs))
      case it if 10 until 20 contains it =>
        DifferentialProduct(nextODE(vars, n-1, lower, v, dotTs=dotTs, funcs=funcs), nextODE(vars, n-1, v, upper, dotTs=dotTs, funcs=funcs))
      case _ => throw new IllegalStateException("random number generator range for ODE generation produces the right range " + r)
    }
  }

  /** Generate a random proof of a random tautological sequent, basically via an external forward sequent calculus */
  def nextPr(vars : IndexedSeq[Variable], n : Int): ProvableSig = {
    require(n>=0)
    if (n == 0 || rand.nextFloat()<=shortProbability) return ProvableSig.startPlainProof(True)(CloseTrue(SuccPos(0)), 0)
    val r = rand.nextInt(70)
    r match {
      case 0 => ProvableSig.startPlainProof(True)(CloseTrue(SuccPos(0)), 0)
      case it if 1 until 10 contains it => val fml = nextF(vars, n - 1); ProvableSig.startPlainProof(Sequent(IndexedSeq(fml), IndexedSeq(fml)))(Close(AntePos(0),SuccPos(0)), 0)
      case it if 10 until 20 contains it => val p1 = nextPr(vars, n-1); val fml = nextF(vars, n-1);
        p1(p1.conclusion.glue(Sequent(IndexedSeq(), IndexedSeq(fml))), HideRight(SuccPos(p1.conclusion.succ.length)))
      case it if 20 until 30 contains it => val p1 = nextPr(vars, n-1); val fml = nextF(vars, n-1);
        p1(p1.conclusion.glue(Sequent(IndexedSeq(fml), IndexedSeq())), HideLeft(AntePos(p1.conclusion.ante.length)))
      case it if 30 until 40 contains it => val p1 = padLeft(vars, n, nextPr(vars, n-1), 2);
        val pos1 = if (p1.conclusion.ante.length<=2) AntePos(0) else AntePos(rand.nextInt(p1.conclusion.ante.length-2))
        p1(Sequent(p1.conclusion.ante.dropRight(2).patch(pos1.getIndex, And(p1.conclusion.ante.dropRight(1).last, p1.conclusion.ante.last)::Nil, 0), p1.conclusion.succ), AndLeft(pos1))
      case it if 40 until 50 contains it => val p1 = padRight(vars, n, nextPr(vars, n-1), 2);
        val pos1 = if (p1.conclusion.succ.length<=2) SuccPos(0) else SuccPos(rand.nextInt(p1.conclusion.succ.length-2))
        p1(Sequent(p1.conclusion.ante, p1.conclusion.succ.dropRight(2).patch(pos1.getIndex, Or(p1.conclusion.succ.dropRight(1).last, p1.conclusion.succ.last)::Nil, 0)),
          OrRight(pos1))
      case it if 50 until 60 contains it => val p1 = padLeft(vars, n, padRight(vars, n, nextPr(vars, n-1), 1), 1);
        val posi1 = rand.nextInt(p1.conclusion.succ.length)
        val pos1 = SuccPos(posi1)
        p1(Sequent(p1.conclusion.ante.patch(p1.conclusion.ante.length-1,Nil,1), p1.conclusion.succ.patch(p1.conclusion.succ.length-1,Nil,1).patch(posi1,
                    Imply(p1.conclusion.ante.last, p1.conclusion.succ.last)::Nil
                    , 0)), ImplyRight(pos1))
      case it if 60 until 65 contains it => val p1 = padLeft(vars, n, nextPr(vars, n-1), 1);
        val pos1 = if (p1.conclusion.succ.isEmpty) 0 else rand.nextInt(p1.conclusion.succ.length)
        p1(Sequent(p1.conclusion.ante.dropRight(1), p1.conclusion.succ.patch(pos1, Not(p1.conclusion(AntePos(p1.conclusion.ante.length-1)))::Nil, 0)),
          NotRight(SuccPos(pos1)))
      case it if 65 until 70 contains it => val p1 = padRight(vars, n, nextPr(vars, n-1), 1);
        val pos1 = if (p1.conclusion.ante.isEmpty) 0 else rand.nextInt(p1.conclusion.ante.length)
        p1(Sequent(p1.conclusion.ante.patch(pos1, Not(p1.conclusion(SuccPos(p1.conclusion.succ.length-1)))::Nil, 0), p1.conclusion.succ.dropRight(1)), NotLeft(AntePos(pos1)))
      case it if 70 until 75 contains it => val p1 = padRight(vars, n, nextPr(vars, n-1), 1); val p2 = padRight(vars, n, nextPr(vars, n-1), 1);
        val pos1 = SuccPos(0) //@todo could do other positions if using ExchangeRight: SuccPos(rand.nextInt(Math.min(p1.conclusion.succ.length, p2.conclusion.succ.length)))
        val (pp1, pp2) = weakenRight(p1, p2, pos1)
        prolong(pp1, pp2, pp1.conclusion.updated(pos1, And(pp1.conclusion(pos1),pp2.conclusion(pos1))), AndRight(pos1))
      //@todo more rules such as AndRight
    }
  }

}
