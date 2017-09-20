package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.AxiomaticODESolver.TIMEVAR
import edu.cmu.cs.ls.keymaerax.btactics.Kaisar.interpret
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.{TPoint => _, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{dW, _}
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXSpec.TPoint
import edu.cmu.cs.ls.keymaerax.btactics.Idioms.?
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import Augmentors._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx._
import edu.cmu.cs.ls.keymaerax.lemma.{LemmaDB, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.{NoProofTermProvable, ProvableSig}
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.collection.immutable

/*
* Proves that CoasterX models meet their specs, by composing component proofs
* @TODO: Function returning tactic with proof repeats
* @TODO: Function returning tactic with proof reuse
* */
class CoasterXProver (spec:CoasterXSpec){

  // Record timing information for a function call so we can measure optimizations to the CoasterX prover
  val MAX_TIMEFN_DEPTH = 10
  var currTimefnDepth = 0
  def timeFn[T](msg:String,f:(()=>T)):T = {
    val start = System.currentTimeMillis()
    currTimefnDepth = currTimefnDepth + 1
    val e = f()
    currTimefnDepth = currTimefnDepth - 1
    val end = System.currentTimeMillis()
    if (currTimefnDepth < MAX_TIMEFN_DEPTH) {
      println("TIME(" + msg + ") " + (end - start) + " millis")
    }
    e
  }

  // Evaluate a Bellerophon snippet, used to get reasonable IntelliJ debugging
  def interpret(e:BelleExpr, pr:Provable):Provable = {
    SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
      case BelleProvable(result,_) => result.underlyingProvable
    }
  }

  // The main loop invariant for a full model
  def invariant(align:(AFile,Formula)):Formula = {
    val (aligned@(points, segments, v0pre, _, inits), segmentDefs) = align
    val v0 = s"($v0pre)*(g()^(1/2))".asTerm
    val nonemptySegs = segments.filter(!spec.segmentEmpty(_))
    val withBounds = spec.zipConsecutive(nonemptySegs, points, inits)
    val ode = withBounds.zipWithIndex.map(spec.segmentOde).reduceRight[Program]({ case (x, y) => Choice(x, y) })
    val y0 = points.head._2
    val energyConserved = s"v^2 + 2*y*g() = ($v0)^2 + 2*($y0)*g()".asFormula
    val globalPost = And("v > 0".asFormula, energyConserved)
    val fml = And(globalPost, withBounds.zipWithIndex.map(spec.segmentPost).reduceRight[Formula] { case (x, y) => And(x, y) })
    fml
  }


  // Establishes differential invariants for a single quadrant-2 arc
  def quad2Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Term, yInit: Term, theta1: Number, deltaTheta: Number,nYs:Int, iSection:Int):Provable = {
    println("Proving Quadrant 2 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    val aproof = arcProofQ2
    // @TODO: Hide preconditions and y-defs that you don't need
    val (cx,cy) = spec.iCenter(iSection)
    val r = spec.iRadius(iSection)
    val ((x0,y0),(x1,y1)) = (p1,p2)
    // Sequent is
    // gConst, defs0, defs1, global, J_i |- post
    // where defs_i = r_i & (cx_i & cy_i) & (dx_i & dy_i)
    def selectDefs:PositionalTactic = "selectDefs" by ((pr:ProvableSig,pos:AntePosition) =>
      NoProofTermProvable(coHideLPr(pos.index0+1, pr.underlyingProvable))
      )
    // definition of r() depends of cx,cy so keep them around too.
    /*def selectR = selectDefs(-2) & andL(-1) & andL(-2) & hideL(-3)
    def selectCx = selectDefs(-2) & andL(-1) & hideL(-1) & andL(-1) & hideL(-2) & andL(-1) & hideL(-2)
    def selectCy = selectDefs(-2) & andL(-1) & hideL(-1) & andL(-1) & hideL(-2) & andL(-1) & hideL(-1)*/
    val (selectR, selectCx, selectCy) = (nil,nil,nil)
    val mainCut = s"(dx=-(($cy)-y)/($r) & dy=(($cx)-x)/($r) & v>0&v^2+2*y*g()=($v0)^2+2*($yInit)*g() & x <= ($cx) & ($cy) <= y & ((x-($cx))^2 + (y-($cy))^2 = ($r)^2))".asFormula
    val pr0 = interpret(dC(mainCut)(1), pr)
    val hide1 = (x0, x1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val cut1 = s"($x1) > ($x0)".asFormula
    val pr1a = timeFn("ArcQ2 Case Step 1", {() => interpret(nil < (nil, cut(cut1) < (nil, hideR(1) & hide1 & QE)), pr0)})
    val hide2 = (y0, y1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val cut3 = s"($y1) > ($y0)".asFormula
    val pr1c = timeFn("ArcQ2 Case Step 3", {() => interpret(nil < (nil, cut(cut3) < (nil, hideR(1) & hide2 & QE)), pr1a)})
    val cut4 = s"($cy) <= ($y0)".asFormula
    val pr1d = timeFn("ArcQ2 Case Step 4", {() => interpret(nil < (nil, cut(cut4) < (nil, hideR(1) & selectCy & QE)), pr1c)})
    val cut5 = s"($x1) <= ($cx)".asFormula
    val pr1e = timeFn("ArcQ2 Case Step 5", {() => interpret(nil < (nil, cut(cut5) < (nil, hideR(1) & selectCx & QE)), pr1d)})
    val cut6 = s"($r) > 0".asFormula
    val pr1f = timeFn("ArcQ2 Case Step 6", {() => interpret(nil < (nil, cut(cut6) < (nil, hideR(1) & selectR & QE)), pr1e)})
    val cut7 = s"((($x0)<=x&x<=($x1)) & (($y0) <= y & y <= ($y1)))->(v^2)/2 > g()*(($y1) - ($y0))".asFormula
    val pr1fa = timeFn("ArcQ2 Case Step 6", {() => interpret(nil < (nil, cut(cut7) < (nil, hideR(1) & QE)), pr1f)})
    val pr1g = interpret(nil <(nil, hideL(-2)*nYs), pr1fa)
    val tac = US(NoProofTermProvable(aproof))
    val pr6 = interpret(nil < (nil, tac), pr1g)
    pr6
  }

  // Establishes differential invariants for a single quadrant-1 arc
  def quad1Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Term, yInit: Term, theta1: Number, deltaTheta: Number,nYs:Int, iSection:Int):Provable = {
    println("Proving Quadrant 1 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    val aproof = arcProofQ1
    val (cx,cy) = spec.iCenter(iSection)
    val r = spec.iRadius(iSection)
    val ((x0,y0),(x1,y1)) = (p1,p2)
    def selectDefs:PositionalTactic = "selectDefs" by ((pr:ProvableSig,pos:AntePosition) =>
      NoProofTermProvable(coHideLPr(pos.index0+1, pr.underlyingProvable))
      )
    // definition of r() depends of cx,cy so keep them around too.
    /*def selectR = selectDefs(-3) & andL(-1) & andL(-2) & hideL(-3)
    def selectCx = selectDefs(-3) & andL(-1) & hideL(-1) & andL(-1) & hideL(-2) & andL(-1) & hideL(-2)
    def selectCy = selectDefs(-3) & andL(-1) & hideL(-1) & andL(-1) & hideL(-2) & andL(-1) & hideL(-1)*/
    val (selectR, selectCx, selectCy) = (nil,nil,nil)
    val mainCut = s"(dx=-(($cy)-y)/($r) & dy=(($cx)-x)/($r) & v>0&v^2+2*y*g()=($v0)^2+2*($yInit)*g() & y >= ($cy)  & ((x-($cx))^2 + (y-($cy))^2 = ($r)^2))".asFormula
    val pr0 = interpret(dC(mainCut)(1), pr)
    val cut1 = s"($x1) > ($x0)".asFormula
    val hide1 = (x0, x1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val pr1a = timeFn("ArcQ1 Case Step 1", {() => interpret(nil < (nil, cut(cut1) < (nil, hideR(1) & hide1 & QE)), pr0)})
    val cut3 = s"($y1) < ($y0)".asFormula
    val hide2 = (y0, y1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val pr1c = timeFn("ArcQ1 Case Step 3", {() => interpret(nil < (nil, cut(cut3) < (nil, hideR(1) & hide2 & QE)), pr1a)})
    val cut4 = s"($cy) <= ($y1)".asFormula
    val pr1d = timeFn("ArcQ1 Case Step 4", {() => interpret(nil < (nil, cut(cut4) < (nil, hideR(1) & selectCy & QE)), pr1c)})
    val cut5 = s"($cx) <= ($x0)".asFormula
    val pr1e = timeFn("ArcQ1 Case Step 5", {() => interpret(nil < (nil, cut(cut5) < (nil, hideR(1) & selectCx & QE)), pr1d)})
    val cut6 = s"($r) > 0".asFormula
    val pr1f = timeFn("ArcQ1 Case Step 6", {() => interpret(nil < (nil, cut(cut6) < (nil, hideR(1) & selectR & QE)), pr1e)})
    val pr1g = interpret(nil <(nil, hideL(-2)*nYs), pr1f)
    val tac = US(NoProofTermProvable(aproof))
    val pr6 = interpret(nil < (nil, tac), pr1g)
    pr6
  }

  // Establishes differential invariants for a single quadrant-3 arc
  def quad3Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Term, yInit: Term, theta1: Number, deltaTheta: Number, nYs:Int, iSection:Int):Provable = {
    println("Proving Quadrant 3 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    val aproof = arcProofQ3
    val ((x0:Term,y0:Term),(x1:Term,y1:Term)) = (p1,p2)
    val (cx,cy) = spec.iCenter(iSection)
    val r = spec.iRadius(iSection)
    val dx0 = s"(($cy)-y)/($r)".asTerm
    val dy0 = s"-(($cx)-x)/($r)".asTerm
    val mainCut = s"(dx=($dx0) & dy=-(($cx)-x)/($r) & v>0&v^2+2*y*g()=($v0)^2+2*($yInit)*g() & v>0 & y < ($cy) & ((x-($cx))^2 + (y-($cy))^2 = ($r)^2))".asFormula
    val pr0 = interpret(dC(mainCut)(1), pr)
    val cut1 = s"($x1) > ($x0)".asFormula
    val hide1 = (x0, x1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val pr1a = timeFn("ArcQ3 Case Step 1", {() => interpret(nil < (nil, cut(cut1) < (nil, hideR(1) & hide1 & QE)), pr0)})
    val cut3 = s"($y0) > ($y1)".asFormula
    val hide2 = (y0, y1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val pr1c = timeFn("ArcQ3 Case Step 3", {() => interpret(nil < (nil, cut(cut3) < (nil, hideR(1) & hide2 & QE)), pr1a)})
    val cut4 = s"($cy) > ($y0)".asFormula
    val pr1d = timeFn("ArcQ3 Case Step 4", {() => interpret(nil < (nil, cut(cut4) < (nil, hideR(1) & QE)), pr1c)})
    val cut5 = s"($cx) >= ($x1)".asFormula
    val pr1e = timeFn("ArcQ3 Case Step 5", {() => interpret(nil < (nil, cut(cut5) < (nil, hideR(1) & QE)), pr1d)})
    val cut6 = s"($r) > 0".asFormula
    val pr1f = timeFn("ArcQ3 Case Step 6", {() => interpret(nil < (nil, cut(cut6) < (nil, hideR(1) & QE)), pr1e)})
    val pr1g = interpret(nil <(nil, hideL(-2)*nYs), pr1f)
    val tac = US(NoProofTermProvable(aproof))
    val pr6 = interpret(nil < (nil, tac), pr1g)
    pr6
  }

  // Establishes differential invariants for a single quadrant-4 arc
  def quad4Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Term, yInit: Term, theta1: Number, deltaTheta: Number,nYs:Int, iSection:Int):Provable = {
    println("Proving Quadrant 4 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    val aproof = arcProofQ4
    val ((x0:Term,y0:Term),(x1:Term,y1:Term)) = (p1,p2)
    val (cx,cy) = spec.iCenter(iSection)
    val r = spec.iRadius(iSection)
    val dx0 = s"(($cy)-y)/($r)".asTerm
    val dy0 = s"-(($cx)-x)/($r)".asTerm
    val Box(ODESystem(_,evol),_) = pr.conclusion.succ.head
    val mainCut = s"(dx=($dx0) & dy=-(($cx)-x)/($r) & v>0&v^2+2*y*g()=($v0)^2+2*($yInit)*g() & v>0 & y < ($cy) & ((x-($cx))^2 + (y-($cy))^2 = ($r)^2))".asFormula
    val pr0 = interpret(dC(mainCut)(1), pr)
    val cut1 = s"($x1) > ($x0)".asFormula
    val hide1 = (x0, x1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val pr1a = timeFn("ArcQ4 Case Step 1", {() => interpret(nil < (nil, cut(cut1) < (nil, hideR(1) & hide1 & QE)), pr0)})
    val cut3 = s"($y1) > ($y0)".asFormula
    val hide2 = (y0, y1) match { case (_:Number, _:Number) => cohideR(1) case _ => nil}
    val pr1c = timeFn("ArcQ4 Case Step 3", {() => interpret(nil < (nil, cut(cut3) < (nil, hideR(1) & hide2 & QE)), pr1a)})
    val cut4 = s"($cy) > ($y1)".asFormula
    val pr1d = timeFn("ArcQ4 Case Step 4", {() => interpret(nil < (nil, cut(cut4) < (nil, hideR(1) & QE)), pr1c)})
    val cut5 = s"($x0) >= ($cx) ".asFormula
    val pr1e = timeFn("ArcQ4 Case Step 5", {() => interpret(nil < (nil, cut(cut5) < (nil, hideR(1) & QE)), pr1d)})
    val cut6 = s"($r) > 0".asFormula
    val pr1f = timeFn("ArcQ4 Case Step 6", {() => interpret(nil < (nil, cut(cut6) < (nil, hideR(1) & QE)), pr1e)})
    val cut7 = s"($evol) -> ((v^2)/2 > g()*(($y1) - ($y0)))".asFormula
    val pr1g = timeFn("ArcQ4 Case Step 7", {() => interpret(nil < (nil, cut(cut7) < (nil, hideR(1) & QE)), pr1f)})
    val pr1i = interpret(nil <(nil, hideL(-2)*nYs), pr1g)
    val tac = US(NoProofTermProvable(aproof))
    val pr6 = interpret(nil < (nil, tac), pr1i)
    pr6
  }


  def coHideL(i : Int, pr:Provable):BelleExpr = {
    val anteSize = pr.subgoals.head.ante.length
    List.tabulate(anteSize)(j => j + 1).filter(j => j != i).map(j => hideL(-j)).foldLeft(nil)((acc,e) => e & acc)
  }

  def coHideLPr(i : Int, pr:Provable):Provable = {
    interpret(coHideL(i,pr), pr)
  }

  // Finish off the arithmetic at the end of a line segment proof more effeciently than a big blind QE
  // @TODO: Everything has changed since this was first implemented - revisit and adjust
  def proveLineArith(pr: Provable, bl:TPoint, tr:TPoint, iSection:Int, nSections:Int):Provable = {
    val (eHide, nYs) = hideYsAfter(iSection, nSections)
    val pr1 = interpret(eHide, pr)
    val pr2 = interpret (implyR(1), pr1)
    val yDefStart = 3
    val Jstart = yDefStart + nYs + 4
    //gConst, defs0, ..., defsn |- rect&glob&post_i
    val dcPos = nYs + 2
    val andPos = nYs + 2
    val pr3 = interpret(andL(-andPos) & andL(-andPos) & andL('Llast) & andL(-andPos) , pr2)
    val pr4 = interpret(andR(1) <(close, nil), pr3)

    def proveConjs(f:(Int,Provable)=>Provable, pr:Provable, conjDepth:Int, conjI:Int = 0):Provable = {
      conjDepth match {
        case 0 => f(conjI,pr)
        case _ =>
          val pr1 = interpret(andR(1), pr)
          val prHead = Provable.startProof(pr1.subgoals.head)
          val prHeadProved = f(conjI, prHead)
          val prTail = pr1(prHeadProved,0)
          proveConjs(f, prTail, conjDepth - 1, conjI + 1)
      }
    }
    // const, yi=_, global(0), post_i(0), t>= 0, DC(t) |- (&_j in sections{bound_j(t) -> post_j(t)}
    def provePost(iPost:Int, pr:Provable):Provable = {
      val Imply(And(LessEqual(x0,_),LessEqual(_,x1)),_) = pr.subgoals.head.succ.head
      val constRange = (x0,x1) match {case(_:Number,_:Number) => true case _ => false}
      val eAggressive = coHideL(dcPos, pr) & implyR(1) & hideR(1) & master()
      val eConservative = {
        val nHides = pr.subgoals.head.ante.length-dcPos
        // gConst, global, ydefs, range, ... |- contradictory_range -> ...
        hideL(-(dcPos+1))*nHides & implyR(1) & hideL(-1) & hideR(1) & master()
      }
      val e:BelleExpr =
        if(iPost == iSection || iPost == iSection + 1) master()
        // For the - 1 case we don't have a contradiction argument (overlaps at one point), but
        // splitting before QE seems to speed up vastly in the cases I've tested
        else if(iPost == iSection - 1) {master()}
        else if(constRange) eAggressive
        else eConservative
      val pr1 = interpret(e, pr)
      pr1
    }
    // yi=_, global(0), post_i(0), t>= 0, DC(t) |- (&_j in sections{bound_j(t) -> post_j(t)}
    val pr9 = proveConjs(provePost, pr4, nSections-1)
    pr9
  }

  def proveArcArith(pr: Provable, bl:TPoint, tr:TPoint, iSection:Int, nSections:Int):Provable = {
    val (eHide, nYs) = hideYsAfter(iSection, nSections)
    val pr1 = interpret(eHide, pr)
    val pr2 = interpret (implyR(1), pr1)
    val yDefStart = 3
    val Jstart = yDefStart + nYs + 4
    //gConst, defs0, ..., defsn |- rect&glob&post_i
    val dcPos = nYs + 2
    val andPos = nYs + 2
    val pr3 = interpret(andL(-andPos) & andL(-andPos) & andL('Llast) & andL(-andPos) & andL('Llast)*4 , pr2)
    val pr4 = interpret(andR(1) <(andR(1)<(close, close), nil), pr3)

    def proveConjs(f:(Int,Provable)=>Provable, pr:Provable, conjDepth:Int, conjI:Int = 0):Provable = {
      conjDepth match {
        case 0 => f(conjI,pr)
        case _ =>
          val pr1 = interpret(andR(1), pr)
          val prHead = Provable.startProof(pr1.subgoals.head)
          val prHeadProved = f(conjI, prHead)
          val prTail = pr1(prHeadProved,0)
          proveConjs(f, prTail, conjDepth - 1, conjI + 1)
      }
    }
    // const, yi=_, global(0), post_i(0), t>= 0, DC(t) |- (&_j in sections{bound_j(t) -> post_j(t)}
    def provePost(iPost:Int, pr:Provable):Provable = {
      val Imply(And(LessEqual(x0,_),LessEqual(_,x1)),_) = pr.subgoals.head.succ.head
      val And(LessEqual(x2,_),LessEqual(_,x3)) = pr.subgoals.head.ante(dcPos-1)
      // @TODO: Fix in lines as well
      val constRange = (x0,x1,x2,x3) match {case(_:Number,_:Number, _:Number, _:Number) => true case _ => false}
      val eAggressive = coHideL(dcPos, pr) & implyR(1) & hideR(1) & master()
      val eConservative = {
        val nHides = pr.subgoals.head.ante.length-dcPos
        // gConst, global, ydefs, range, ... |- contradictory_range -> ...
        hideL(-(dcPos+1))*nHides & implyR(1) & hideL(-1) & hideR(1) & master()
      }
      val e:BelleExpr =
        if(iPost == iSection || iPost == iSection + 1) master()
        // For the - 1 case we don't have a contradiction argument (overlaps at one point), but
        // splitting before QE seems to speed up vastly in the cases I've tested
        else if(iPost == iSection - 1) {master()}
        else if(constRange) eAggressive
        else eConservative
      val pr1 = interpret(e, pr)
      pr1
    }
    // yi=_, global(0), post_i(0), t>= 0, DC(t) |- (&_j in sections{bound_j(t) -> post_j(t)}
    val pr9 = proveConjs(provePost, pr4, nSections-1)
    pr9
  }

  // Finish off the arithmetic at the end of a line segment proof more effeciently than a big blind QE, assuming the
  // solvable ODE was proved using dI and dW instead of solve()
  def proveLineArithFromDW(pr: Provable, bl:TPoint, tr:TPoint, iSection:Int, nSections:Int):Provable = {
    val yDefStart = 3
    val nYs = {
      val js = List.tabulate(nSections)(j => j + yDefStart).filter(j => !(j == iSection + yDefStart || j == iSection + yDefStart - 1 || j == iSection + yDefStart - 2))
      nSections - js.length
    }
    val Jstart = yDefStart + nYs + 4
    val hideJs = {
      val js = List.tabulate(nSections)(j => j + Jstart).filter(j => j != Jstart + iSection)
      js.map(i => hideL(-i)).foldLeft(nil)((acc, e) => e & acc)
    }
    // const, yi=_, global(0), (op,)_j in sections{bound_j(0) -> post_j(0)} |- " "
    val pr4 = selectSection(iSection,nSections,pr)
    // const, yi=_, global(0), (bound_i(0) -> post_i(0)), t >= 0, (\forall s in [0,t] DC) |- J(t)
    val pr6 = interpret(implyL(-Jstart) <((hideL(-2)*(nYs+1)) & hideR(1) & master(), nil), pr4)
    val proveGlobal = allL(Number(0))('Llast) & master()
    // const,  yi=_, global(0), post_i(0), t>= 0, (\forall s in [0,t] DC) |- (global(t) & (&_j in sections{bound_j(t) -> post_j(t)})
    val pr7 = interpret(dW(1), pr6)
    val dcPos = 6
    def coHideL(i : Int, pr:Provable) = {
      val anteSize = pr.subgoals.head.ante.length
      List.tabulate(anteSize)(j => j + 1).filter(j => j != i).map(j => hideL(-j)).foldLeft(nil)((acc,e) => e & acc)
    }
    // const,  yi=_, global(0), post_i(0), t>= 0, (\forall s in [0,t] DC) |- (&_j in sections{bound_j(t) -> post_j(t)}
    val pr8 = interpret(allL(Variable("t_"))(-dcPos) & implyL(-dcPos) <(coHideL(dcPos - 1, pr7) & hideR(1) & QE, nil), pr7)
    def proveConjs(f:(Int,Provable)=>Provable, pr:Provable, conjDepth:Int, conjI:Int = 0):Provable = {
      conjDepth match {
        case 0 => f(conjI,pr)
        case _ =>
          val pr1 = interpret(andR(1), pr)
          val prHead = Provable.startProof(pr1.subgoals.head)
          val prHeadProved = f(conjI, prHead)
          val prTail = pr1(prHeadProved,0)
          proveConjs(f, prTail, conjDepth - 1, conjI + 1)
      }
    }
    // const, yi=_, global(0), post_i(0), t>= 0, DC(t) |- (&_j in sections{bound_j(t) -> post_j(t)}
    def provePost(iPost:Int, pr:Provable):Provable = {
      val e:BelleExpr =
        if(iPost == iSection || iPost == iSection + 1) QE
        // For the - 1 case we don't have a contradiction argument (overlaps at one point), but
        // splitting before QE seems to speed up vastly in the cases I've tested
        else if(iPost == iSection - 1) {master()}
        else {coHideL(dcPos, pr) & implyR(1) & hideR(1) & QE}
      val pr1 = interpret(e, pr)
      pr1
    }
    // yi=_, global(0), post_i(0), t>= 0, DC(t) |- (&_j in sections{bound_j(t) -> post_j(t)}
    val pr9 = proveConjs(provePost, pr7, nSections-1)
    pr9
  }

  // Storage for component proofs
  val lemmaDB: LemmaDB = LemmaDBFactory.lemmaDB
  def storeLemma(fact: ProvableSig, name: Option[String]): String = {
    val evidence = ToolEvidence(immutable.List("input" -> fact.conclusion.prettyString, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val id = lemmaDB.add(Lemma(fact, evidence, name))
    println(s"Lemma ${name.getOrElse("")} stored as $id")
    id
  }

  // Proof of generic straight component
  lazy val straightProof:Provable = {
    val provableName = "coasterx_straightLineCase"
    lemmaDB.get(provableName) match {
      case Some(pr) => pr.fact.underlyingProvable
      case None =>
        val a1: Formula = "(g() > 0)".asFormula
        val a2: Formula = "(v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g())".asFormula
        val a3: Formula = "(x0()<=x&x<=x1()->(dx0()*y=dy0()*x+dx0()*c()))".asFormula
        val a5: Formula = "((x0()<=x&x<=x1()) & (y0() <= y & y <= y1())) -> dx0()*v^2 > 2*(x1()-x0())*dy0()*g()".asFormula
        val a6: Formula = "(x1() > x0())".asFormula
        val a7: Formula = "(dx0()^2 + dy0()^2 = 1)".asFormula
        val a8: Formula = "dx0() > 0".asFormula
        val c =
          """  [{x'=v*dx0(),
          |        y'=v*dy0(),
          |        v'=-dy0()*g()
          |        &(x0()<=x&x<=x1())
          |        &(y0()<=y&y<=y1())}]
          |     ((v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g())&
            |      x0()<=x&x<=x1()
            |      &dx0()*y=dy0()*x+dx0()*c())""".stripMargin.asFormula
        val con:Sequent = Sequent(immutable.IndexedSeq(a1,a2,a3,a5, a6, a7, a8), immutable.IndexedSeq(c))
        val e =
          //(composeb(1) & assignb(1)) &
          //(composeb(1) & assignb(1)) &
           solve(1) & allR(1) & implyR(1) & implyR(1) &
             implyL(-2)  <(
               hideR(1) & QE,
               master()
             )

        val pr = Provable.startProof(con)
        val pr1 = interpret(TactixLibrary.unfoldProgramNormalize, pr)
        val pr2 = interpret(e, pr1)
        storeLemma(NoProofTermProvable(pr2), Some(provableName))
        pr2
        }
  }

  // Proof of generic quadrant-1 arc
  lazy val arcProofQ1:Provable = {
    val provableName = "coasterx_Q1ArcCase"
    lemmaDB.get(provableName) match {
      case Some(pr) => pr.fact.underlyingProvable
      case None =>
        val a1 = "g() > 0".asFormula
        val a2 = "(v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g())".asFormula
        val a3 = "(x0()<=x&x<=x1()->((((x-cx())^2 + (y-cy())^2 = r()^2 &(cx()<=x & cy()<=y))))".asFormula
        val a4 = "x1() > x0()".asFormula
        val a6 = "y1() < y0()".asFormula
        val a7 = "cy() <= y1()".asFormula
        val a8 = "cx() <= x0()".asFormula
        val a9 = "r() > 0".asFormula
        val c =
          """[dx:=-(cy()-y)/r(); dy:=(cx()-x)/r()) ;{x'=dx*v,
            |            y'=dy*v,
            |            v'=-dy*g(),
            |            dx' =  dy*v/r(),
            |            dy' =  (-dx*v)/r()
            |            &(x0()<=x&x<=x1())
            |            &(y1()<=y&y<=y0())}]
            |        ( dx=-(cy()-y)/r()
            |          & dy=(cx()-x)/r()
            |          & v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g()
            |          & y >= cy()
            |          & ((x-cx())^2 + (y-cy())^2 = r()^2)
            |          )""".stripMargin.asFormula
        val con:Sequent = Sequent(immutable.IndexedSeq(a1, a2, a3, a4, a6, a7, a8,a9), immutable.IndexedSeq(c))
        val pr = Provable.startProof(con)
        val pr1 = interpret(TactixLibrary.unfoldProgramNormalize, pr)
        val pr1a = interpret((composeb(1) & assignb(1)) &
            (composeb(1) & assignb(1)), pr1)
        val pr2 = interpret(dC("dx=-(cy()-y)/r()".asFormula)(1) <(nil, dI()(1)), pr1a)
        val pr3 = interpret(dC("dy=(cx()-x)/r()".asFormula)(1) <(nil, dI()(1)), pr2)
        val pr4 = interpret(dC("v^2=v0()^2+2*yGlobal()*g()-2*y*g()".asFormula)( 1)  <(nil, dI()(1)), pr3)
        val pr5 = interpret(dC("v>0".asFormula)(1) <(nil, ODE(1)), pr4)
        val pr6 = interpret(dC("(x-cx())^2 + (y-cy())^2 = r()^2".asFormula)(1) <(nil, ODE(1)), pr5)
        val pr7 = interpret(ODE(1), pr6)
        storeLemma(NoProofTermProvable(pr7), Some(provableName))
        pr7
    }
  }


  // Proof of generic quadrant-2 arc
  lazy val arcProofQ2:Provable = {
    val provableName = "coasterx_Q2ArcCase"
    lemmaDB.get(provableName) match {
      case Some(pr) => pr.fact.underlyingProvable
      case None =>
        val a1 = "g() > 0".asFormula
        val a2 = "(v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g())".asFormula
        val a3 = "(x0()<=x&x<=x1()->((((x-cx())^2 + (y-cy())^2 = r()^2 &(x<=cx() & cy()<=y))))".asFormula
        val a4 = "x1() > x0()".asFormula
        val a6 = "y1() > y0()".asFormula
        val a7 = "cy() <= y0()".asFormula
        val a8 = "x1() <= cx() ".asFormula
        val a9 = "r() > 0".asFormula
        val a10 = "((x0()<=x&x<=x1()) & (y0() <= y & y <= y1()))->(v^2)/2 > g()*(y1() - y0())".asFormula
        val c =
          """[dx:=-(cy()-y)/r() ; dy:=(cx()-x)/r()) ;{x'=dx*v,
            |            y'=dy*v,
            |            v'=-dy*g(),
            |            dx' =  (dy*v)/r(),
            |            dy' =  (-dx*v)/r()
            |            &(x0()<=x&x<=x1())
            |            &(y0()<=y&y<=y1())}]
            |          ( dx=-(cy()-y)/r()
            |          & dy=(cx()-x)/r()
            |          & v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g()
            |          & x <= cx()
            |          & cy() <= y
            |          & ((x-cx())^2 + (y-cy())^2 = r()^2)
            |          )""".stripMargin.asFormula
        val con:Sequent = Sequent(immutable.IndexedSeq(a1, a2, a3, a4, a6, a7, a8,a9, a10), immutable.IndexedSeq(c))
        val pr = Provable.startProof(con)
        val cy = "cy()".asTerm
        val v0 = "v0()".asTerm
        val r = "r()".asTerm
        val cx = "cx()".asTerm
        val yInit = "yGlobal()".asTerm

        // Note: Conservation of energy always uses the start of the ENTIRE track, not current section
        val ECirc:Formula = s"v^2=($v0)^2+2*($yInit)*g()-2*y*g()".asFormula
        val dGDefined:Formula = s"2*v!=0".asFormula
        val pr1:Provable = interpret(composeb(1) & assignb(1) & composeb(1) & assignb(1), pr)
        val pr2:Provable = interpret(dC(s"dx^2 + dy^2 = 1".asFormula)(1)    <(nil, dI()(1)), pr1)
        val pr3:Provable = interpret(dC(s"dx=(y-($cy))/($r)".asFormula)(1) <(nil, dI()(1)), pr2)
        val pr4:Provable = interpret(dC(s"dy=-(x-($cx))/($r)".asFormula)(1)  <(nil, dI()(1)), pr3)
        val pr5:Provable = interpret(dC(ECirc)('R) <(nil, dI()(1)), pr4)
        val pr5a:Provable = interpret(dC(s"(v^2)/2 > g()*(y1() - y)".asFormula)(1) <(nil, dI()(1)), pr5)
        val pr6:Provable = interpret(dC("v>0".asFormula)('R), pr5a)
        val pr7:Provable = interpret(nil <(nil, dC(dGDefined)(1)), pr6)
        val pr8:Provable = interpret(nil <(nil, dG(s"{a'=((dy*g())/(2*v))*a+0}".asDifferentialProgram, Some("a^2*v=1".asFormula))(1), nil), pr7)
        val pr9:Provable = interpret(nil <(nil, existsR("(1/v)^(1/2)".asTerm)(1), nil), pr8)
        val pr10:Provable = interpret(nil <(nil, dI()(1), nil), pr9)
        val pr11:Provable = interpret(nil <(nil, ODE(1)), pr10)
        val pr12 = interpret(ODE(1), pr11)
        storeLemma(NoProofTermProvable(pr12), Some(provableName))
        pr12
    }
  }

  // Proof of generic quadrant-3 arc
  lazy val arcProofQ3:Provable = {
    val provableName = "coasterx_Q3ArcCase"
    lemmaDB.get(provableName) match {
      case Some(pr) => pr.fact.underlyingProvable
      case None =>
        val a1 = "g() > 0".asFormula
        val a2 = "(v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g())".asFormula
        val a3 = "(x0()<=x&x<=x1()->(( ((x-cx())^2 + (y-cy())^2 = r()^2 &(x<=cx() & y<=cy()))))".asFormula
        val a4 = "x1() > x0()".asFormula
        val a6 = "y0() > y1()".asFormula
        val a7 = "cy() > y0()".asFormula
        val a8 = "cx() >= x1()".asFormula
        val a9 = "r() > 0".asFormula
        val c =
          """[dx:=-(y-cy())/r()  ; dy:=(x-cx())/r()) ;{x'=dx*v,
            |            y'=dy*v,
            |            v'=-dy*g(),
            |            dx' =  (-dy*v)/r(),
            |            dy' =  dx*v/r()
            |            &(x0()<=x&x<=x1())
            |            &(y1()<=y&y<=y0())}]
            |        ( dx=(cy()-y)/r()
            |          & dy=-(cx()-x)/r()
            |          & v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g()
            |          & v>0
            |          & y < cy()
            |          & ((x-cx())^2 + (y-cy())^2 = r()^2)
            |          )""".stripMargin.asFormula
        val con:Sequent = Sequent(immutable.IndexedSeq(a1, a2, a3, a4, a6, a7, a8,a9), immutable.IndexedSeq(c))
        val e =
          composeb(1) & assignb(1) & composeb(1) & assignb(1) &
          dC("dx=-(y-cy())/r()".asFormula)(1) <(nil, dI()(1)) &
          dC("dy=(x-cx())/r()".asFormula)(1) <(nil, dI()(1)) &
          dC("v^2=v0()^2+2*yGlobal()*g()-2*y*g()".asFormula)( 1)  <(nil, dI()(1)) &
          dC("v>0".asFormula)(1) <(nil, ODE(1)) &
          dC("(x-cx())^2 + (y-cy())^2 = r()^2".asFormula)(1) <(nil, ODE(1)) &
          ODE(1)
        val pr = Provable.startProof(con)
        val pr1 = interpret(TactixLibrary.unfoldProgramNormalize, pr)
        val pr2 = interpret(e, pr1)
        storeLemma(NoProofTermProvable(pr2), Some(provableName))
        pr2
    }
  }

  // Proof of generic quadrant-4 arc
  lazy val arcProofQ4:Provable = {
    val provableName = "coasterx_Q4ArcCase"
    lemmaDB.get(provableName) match {
      case Some(pr) => pr.fact.underlyingProvable
      case None =>
        val a1 = "g() > 0".asFormula
        val a2 = "(v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g())".asFormula
        val a3 = "(x0()<=x&x<=x1()->((((x-cx())^2 + (y-cy())^2 = r()^2 &(cx()<=x & y<=cy()))))".asFormula
        val a4 = "x1() > x0()".asFormula
        val a6 = "y1() > y0()".asFormula
        val a7 = "cy() > y1()".asFormula
        val a8 = "x0() >= cx()".asFormula
        val a9 = "r() > 0".asFormula
        val a10 = "((x0()<=x&x<=x1()) & (y0() <= y & y <= y1()))->(v^2)/2 > g()*(y1() - y0())".asFormula
        val c =
          """[dx:=-(y-cy())/r(); dy:=(x-cx())/r()); {x'=dx*v,
            |            y'=dy*v,
            |            v'=-dy*g(),
            |            dx' =  (-dy*v)/r(),
            |            dy' =  dx*v/r()
            |            &(x0()<=x&x<=x1())
            |            &(y0()<=y&y<=y1())}]
            |        ( dx=(cy()-y)/r()
            |          & dy=-(cx()-x)/r()
            |          & v>0&v^2+2*y*g()=v0()^2+2*yGlobal()*g()
            |          & v>0
            |          & y < cy()
            |          & ((x-cx())^2 + (y-cy())^2 = r()^2)
            |          )""".stripMargin.asFormula
        val con:Sequent = Sequent(immutable.IndexedSeq(a1, a2, a3, a4, a6, a7, a8,a9, a10), immutable.IndexedSeq(c))
        val pr = Provable.startProof(con)
        val cy = "cy()".asTerm
        val v0 = "v0()".asTerm
        val r = "r()".asTerm
        val cx = "cx()".asTerm
        val yInit = "yGlobal()".asTerm
        val pr0 = interpret(composeb(1) & assignb(1) & composeb(1) & assignb(1), pr)
        val pr1 = interpret(dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)), pr0)
        val pr2 = interpret(dC(s"dy=(x-($cx))/($r)".asFormula)( 1)  <(nil, ODE(1)), pr1)
        val pr3 = interpret(dC(s"($cx)<=x".asFormula)(1)  <(nil, ODE(1)), pr2)
        val pr3a = interpret(dC(s"g() > 0".asFormula)(1) <(nil, dI()(1)), pr3)
        val pr4 = interpret(dC(s"v^2=($v0)^2+2*($yInit)*g()-2*y*g()".asFormula)(1) <(nil, dI()(1)), pr3a)
        val pr5 = interpret(dC(s"(($cx)-x)^2+(($cy)-y)^2=($r)^2".asFormula)(1) <(nil, DebuggingTactics.debug("This dI is slow", doPrint = true) & dI()(1)), pr4)
        val pr6 = interpret(dC(s"y < ($cy)".asFormula)(1) <(nil,
          dC(s"2*(y-($cy))*($r)!=0".asFormula)(1)  <(
            dG(s"{a'=(($cx)-x)*v/(2*(y-($cy))*($r))*a+0}".asDifferentialProgram, Some(s"a^2*(y-($cy))=-1".asFormula))(1) &
              existsR(s"(-1/(y-($cy)))^(1/2)".asTerm)(1) &
              ODE(1),
            ODE(1)
          )
        ), pr5)
        val pr6a = interpret(dC(s"(v^2)/2 > g()*(y1() - y)".asFormula)(1) <(nil, ODE(1)), pr6)
        val pr7 = interpret(dC(s"v>0".asFormula)(1)  <(nil,
          DebuggingTactics.debug("foo", doPrint = true) &
          dC(s"2*v!=0".asFormula)(1)  <(
            DebuggingTactics.debug("bar", doPrint = true) &
            dG(s"{a'=((dy*g())/(2*v))*a+0}".asDifferentialProgram, Some("a^2*v=1".asFormula))(1) &
              existsR("(1/v)^(1/2)".asTerm)(1) &
              DebuggingTactics.debug("This dI doesn't prove", doPrint = true) &
              DebuggingTactics.debug("bat", doPrint = true) &
              dI()(1),
            DebuggingTactics.debug("baz", doPrint = true) &
            ODE(1)
          )
        ), pr6a)
        val pr8 = interpret(ODE(1), pr7)
        storeLemma(NoProofTermProvable(pr8), Some(provableName))
        pr8
    }
  }

  def hideYs(iSection:Int, nSections:Int):(BelleExpr, Int) = {
    //@TODO: This hid too much, so now hiding notihng
    (nil, nSections)

  }

  def hideYsAfter(iSection:Int, nSections:Int, yDefStart:Int = 2):(BelleExpr, Int) = {
    val js = List.tabulate(nSections)(j => j + yDefStart).filter(j => j > iSection + yDefStart + 1)
    val e = js.map(i => hideL(-i)).foldLeft(nil)((acc, e) => e & acc)
    (e, nSections - js.length)
  }

  // TODO: document
  def selectSection(iSection:Int, nSections:Int, pr:Provable):Provable = {
    val gStart = 2
    val JStart = 1
    val yDefStart = 3
    val (hideYDefs, nYs) = hideYs(iSection,nSections)
    // J(0),const, y_1=_,...,y_n=_ |- _
    val pr1 = interpret(hideYDefs, pr)
    // J(0), const,y_i=_ |- _
    val pr2 = interpret(andL(-JStart), pr1)
    val unpackPosts = andL('Llast)*(nSections - 1)
    //const, y_i=_, global(0), &(bound_i(0) -> post_i(0)) |- _
    val pr3 = interpret(unpackPosts, pr2)
    val Jstart = yDefStart + nYs
    val hideJs = {
      val js = List.tabulate(nSections)(j => j + Jstart).filter(j => j != Jstart + iSection)
      js.map(i => hideL(-i)).foldLeft(nil)((acc, e) => e & acc)
    }
    //const, y_i=_, global(0), (bound_0(0) -> post_0(0)), ...,  (bound_n(0) -> post_n(0)) |- _
    val pr4 = interpret(hideJs, pr3)
    pr4
  }

  // Proves any one section
  def sectionTactic(pr: Provable, p1: TPoint, p2: TPoint, v0:Term, yInit:Term, section: Section, iSection:Int, nSections: Int, initD:TPoint):Provable = {
    val nYs = hideYs(iSection, nSections)._2
    section match {
      case ArcSection(Some(param@ArcParam(bl,tr,theta1,deltaTheta)),Some(grad)) => {
        val (t1, t2) = (theta1.value, param.theta2.value)
        val q3 = t1 <= -90 && t2 <= -90
        val q4 = t1 >= -90 && t1 <= 0   && t2 <= 0
        val q1 = t1 >= 0   && t1 <= 90  && t2 <= 90
        val prStart = selectSection(iSection,nSections, pr)
        val pr1 =
          (q3, q4, q1) match {
            case (true, false, false) =>
              timeFn("Q3", () => {
              quad3Tactic(prStart, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta,nYs, iSection)}) // Quadrant 3
            case (false, true, false) =>
              timeFn("Q4", () => {
              quad4Tactic(prStart, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta,nYs, iSection)
              }) // Quadrant 4
            case (false, false, true) =>
              timeFn("Q1", () => {
                quad1Tactic(prStart, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta,nYs, iSection)}) // Quadrant 1
            case (false,false,false)  =>
              timeFn("Q2", () => {
              quad2Tactic(prStart, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta,nYs, iSection)})
               // Quadrant 2
            case _ => ???
          }
        val prOut =
          timeFn("Arc QE", () => {
            interpret(dW(1), pr1)})
        val prOut2 = proveArcArith(prOut,bl,tr,iSection,nSections)
        assert(prOut2.isProved)
        prOut2
      }
      case LineSection(Some(LineParam(bl,tr)), Some(grad), isUp) => {
        println(isUp)
        val t = Variable("kyxtime")
        def cutSolve() = {
          val pr1 = interpret(AxiomaticODESolver.addTimeVar(1), pr)
          val pr1a = interpret(assignb(1), pr1)
          val pr2 = interpret(dC(s"v = old(v) - dy*($t)".asFormula)(1) <(nil, dI()(1)), pr1a)
          val pr3 = interpret(dC(s"y = old(y) + dy*(old(v)*($t) - dy*($t)^2/2)".asFormula)(1) <(nil, dI()(1)), pr2)
          val pr4 = interpret(dC(s"x = old(x) + dx*(old(v)*($t) - dy*($t)^2/2)".asFormula)(1) <(nil, dI()(1)), pr3)
          pr4
        }
        def doLineCase () = {
          println("Proving Line Segment: ", bl, tr)
          //const, y_i=_, global(0), (bound_0(0) -> post_0(0)), ...,  (bound_n(0) -> post_n(0)) |- _
          val pr4 = selectSection(iSection,nSections,pr)
          //const, y_i=_, global(0), bound_i(0) -> post_i(0))|- _
          val x1 = tr._1
          val x0 = bl._1
          val y0 = bl._2
          val y1 = tr._2
          val Box(Compose(Assign(BaseVariable("dx", None, Real), dx0),Compose(Assign(BaseVariable("dy", None, Real),dy0),ODESystem(_, constr))),_) = pr.conclusion.succ.head//s"(($x0) <= x & x <= ($x1))&(($y0) <= y & y <= ($y1))".asFormula
          val thisInv = spec.segmentPost((section, (bl,tr), initD),iSection)
          val Imply(_, Equal(_, Plus(_, c))) = thisInv
          val HY = hideYsAfter(iSection, nSections)._1
          //val asgn = DLBySubst.assignEquality
          val asgn = assignb
          val cutMain = s"(v>0&v^2+2*y*g()=($v0)^2+2*($yInit)*g())&(($x0)<=x&x<=($x1)&($dx0)*y=($dy0)*x+($c))".asFormula
          val pr4a = interpret(composeb(1) & asgn(1), pr4)
          val pr4b = interpret(composeb(1) & asgn(1), pr4a)
          val dxDefPos1 = pr4b.subgoals.head.ante.length-1
          val pr5 = interpret(dC(cutMain)(1), pr4b)
          val sproof = straightProof
          val cut1 = s"($constr) -> (($dx0)*v^2 > 2*(($x1)-($x0))*($dy0)*g())".asFormula
          val pr5a = timeFn("Line Case Step 1", {() => interpret(nil < (nil, cut(cut1) < (nil, hideR(1) & HY & QE)), pr5)})
          val cut2 = s"($x1) > ($x0)".asFormula
          val hide2 = (x0, x1) match {case (_:Number, _:Number) => cohideR(1) case _ => nil}
          val pr5b = timeFn("Line Case Step 2", {() => interpret(nil < (nil, cut(cut2) < (nil, hideR(1) & hide2 & QE)), pr5a)})
          val cut3 = s"($dx0)^2 + ($dy0)^2 = 1".asFormula
          val pr5c = timeFn("Line Case Step 3", {() => interpret(nil < (nil, cut(cut3) < (nil, hideR(1) & HY & QE)), pr5b)})
          val cut4 = s"($dx0) > 0".asFormula
          val pr5d = timeFn("Line Case Step 4", {() => interpret(nil < (nil, cut(cut4) < (nil, hideR(1) & HY & QE)), pr5c)})
          val pr5e = timeFn("Line Case Step 5", {() => interpret(nil < (nil, hideL(-2)*nYs), pr5d)})
          val dxDefPos2 = dxDefPos1 - nYs
          //val pr5f = timeFn("Line Case Step 5a", {() => interpret(nil < (nil, hideL(-dxDefPos2)*2), pr5e)})
          val tac = US(NoProofTermProvable(sproof))
          val pr6 = interpret(nil < (nil, tac), pr5e)
          val pr6a = timeFn("Line Case Step 6", {() => interpret(dW(1), pr6)})
          //@TODO: Don't think need to hide anything because case selection already hides
          val (eHide,_) = hideYs(iSection, nSections)
          val pr7 = timeFn("Line Case Step 7", {() => interpret(eHide , pr6a)})
          val pr8 = timeFn("Line Case Step 8", {() =>
            //interpret(master(), pr7)
            proveLineArith(pr7,bl,tr,iSection,nSections)
            })
          pr8
        }
        timeFn("Line Case", doLineCase)
      }
      case _ => ???
    }
  }

  def provePosts(pr:Provable, fml:Formula, p1: TPoint, p2: TPoint, section: Section, v: Number, yInit: Term, i: Int, j:Int, nSections:Int, initD:TPoint):BelleExpr = {
    val thisE =
      if(i == j) {
        sectionTactic(pr, p1, p2, v, yInit,section, i, nSections, initD)
        //@TODO: fix
        nil
      } else {
        dW(1) & QE
      }
    fml match {
      case And(p,q) => andR(1) <(thisE, provePosts(pr, q, p1, p2, section, v, yInit,i, j+1, nSections, initD))
      case _ => thisE
    }
  }

  def componentTactic(pr:Provable, p1: TPoint, p2: TPoint, section: Section, v: Term, yInit: Term, i: Int, nSections:Int, initD:TPoint):Provable = {
    sectionTactic(pr, p1, p2, v, yInit, section, i, nSections, initD)
  }

  def proveAllComponents(global:Provable, locals: List[Provable], points: List[(Term, Term)], segments: List[Section], v: Term, yInit: Term, i: Int, nSections: Int, initsD:List[TPoint]):Provable = {
    (points, segments, locals, initsD) match {
      case (p1 :: p2 :: Nil, s1 :: Nil, pr :: Nil, d :: Nil) => componentTactic(pr, p1, p2, s1, v, yInit, i, nSections, d)
      case (p1 :: p2 :: ps, s1 :: ss, pr :: prs, d::ds) =>
        val sg = componentTactic(pr, p1, p2, s1, v, yInit, i, nSections,d)
        val plugged = global(sg, 0)
        proveAllComponents(plugged, prs, p2::ps, ss, v, yInit, i+1, nSections,ds)
      case _ => ???
    }
  }

  def splitComponents(pr:Provable,i:Int = 0):(Provable, List[Provable]) = {
    pr.subgoals.head.succ.head match {
      case (Box(Choice(_,_), _)) =>
        val pr1 = interpret(choiceb(1) & andR(1), pr)
        val sgHead = Provable.startProof(pr1.subgoals(0))
        val sgTail = Provable.startProof(pr1.subgoals(1))
        val (global, locals) = splitComponents(sgTail, i+1)
        (pr1(global,1), sgHead::locals)
      case  _ =>
        (pr, Provable.startProof(pr.subgoals.last) :: Nil)
    }
  }

  // Rotate all antecedent formulas to the left by 1
  def rotAnte(pr:Provable):Provable = {
    val fml = pr.subgoals.head.ante.head
    interpret(cut(fml) <(hideL(-1), close), pr)
  }

  // Prove an entire CoasterX model from scratch
  def apply(fileName:String):Provable = {
    val parsed = CoasterXParser.parseFile(fileName).get
    val align@(aligned@(points, segments, v0pre, _, ds), segmentDefs) = spec.prepareFile(parsed)
    val v0 = s"($v0pre)*(g()^(1/2))".asTerm
    val specc = spec.fromAligned(align)
    val nSections = segments.length-1
    val pr = Provable.startProof(specc)
    val pr1 = interpret(implyR(1), pr)
    // _ |- [a]post
    val pr1a = interpret(andL(-1), pr1)
    // localConsts,(globalConst&initState) |-
    val pr1b = interpret(andL(-2), pr1a)
    // localConsts,globalConst,initState   |-
    val pr1c = if (nSections > 1) interpret(andL(-1), pr1b) else rotAnte(pr1b)
    // globalConst,initState, lc1, &_2^n {lc_i}   |-
    val unpackLocalConsts = List.tabulate(nSections-2){case i => andL(-(i+4))}.foldLeft(nil)((acc,e) => acc & e)
    val pr1e = interpret(unpackLocalConsts, pr1c)
    val inv = invariant(align)
    val pr2 = interpret(DLBySubst.loop(inv, pre = nil)(1), pr1e)
    val pr3 = interpret(nil <((alphaRule*) & QE, nil, nil), pr2)
    val pr3a = interpret(nil <((alphaRule*), nil), pr3)
    val pr4 = interpret(nil <(master(), nil), pr3a)
    val (globalPr, localPrs) = splitComponents(pr4)
    val prEnd = proveAllComponents(globalPr, localPrs, points, segments.tail, v0, points.head._2, 0, segments.tail.length, ds)
    assert(prEnd.isProved, "CoasterX model not proved")
    prEnd
  }
}
