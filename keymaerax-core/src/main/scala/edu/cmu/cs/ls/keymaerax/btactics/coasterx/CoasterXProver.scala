package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{AxiomaticODESolver, DebuggingTactics}
import edu.cmu.cs.ls.keymaerax.btactics.AxiomaticODESolver.TIMEVAR
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.{TPoint => _, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{dW, _}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXSpec._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.NoProofTermProvable

/*
* Proves that CoasterX models meet their specs, by composing component proofs
* @TODO: Comute one v0 value and use it everywhere. Show that v0 is big enough to match all the heights
* @TODO: Support all examples from test suite
* @TODO: Function returning provable, with proof repeats
* @TODO: Function returning provable, with proof reuse
* @TODO: Function returning tactic with proof repeats
* @TODO: Function returning tactic with proof reuse
* */
object CoasterXProver {
  def interpret(e:BelleExpr, pr:Provable):Provable = {
    SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
      case BelleProvable(result,_) => result.underlyingProvable
    }
  }

  def invariant(align:(File,Formula)):Formula = {
    val (aligned@(points, segments, v0, _), segmentDefs) = align
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive(nonemptySegs, points)
    val ode = withBounds.map(segmentOde).reduceRight[Program]({ case (x, y) => Choice(x, y) })
    val y0 = points.head._2
    val energyConserved = s"v^2 + 2*y = ($v0)^2 + 2*($y0)".asFormula
    val globalPost = And("v > 0".asFormula, energyConserved)
    val fml = And(globalPost, withBounds.map(segmentPost).reduceRight[Formula] { case (x, y) => And(x, y) })
    fml
  }

  def quad2Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, yInit: Term, theta1: Number, deltaTheta: Number):Provable = {
    //val xLim:Formula = s"x<=($cx)".asFormula
    //val yLim:Formula = s"y<=($yEnd)".asFormula
    //val cyLim:Formula = s"($cy) < ($yEnd)".asFormula
    //val pr1:Provable = interpret(normalize, pr)
    println("Proving Quadrant 2 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    // @TODO: Set cx, cy to correct value as done in postcondition generator
    // @TODO: Hide preconditions and y-defs that you don't need
    val (cx:Term, cy:Term) = arcCenter(bl, tr)
    val r = CoasterXSpec.dist(p1, (cx,cy))
    //val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    //val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    //val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    // Note: Conservation of energy always uses the start of the ENTIRE track, not current section
    val ECirc:Formula = s"v^2=($v0)^2+2*($yInit)-2*y&(($cx)-x)^2+(($cy)-y)^2=($r)^2".asFormula
    val dGDefined:Formula = s"2*v*($r)!=0".asFormula
    val pr2:Provable = interpret(dC(s"dx^2 + dy^2 = 1".asFormula)(1)    <(nil, dI()(1)), pr)
    val pr3:Provable = interpret(dC(s"dx=(y-($cy))/($r)".asFormula)(1) <(nil, dI()(1)), pr2)
    val pr4:Provable = interpret(dC(s"dy=-(x-($cx))/($r)".asFormula)(1)  <(nil, dI()(1)), pr3)
    val pr5:Provable = interpret(dC(ECirc)('R) <(nil, dI()(1)), pr4)
    val pr6:Provable = interpret(dC("v>0".asFormula)('R), pr5)
    val pr7:Provable = interpret(nil <(nil, dC(dGDefined)(1)), pr6)
    val pr8:Provable = interpret(nil <(nil, dG(AtomicODE(DifferentialSymbol(Variable("a")), s"((($cx)-x)/(2*v*($r)))*a+0".asTerm), Some("a^2*v=1".asFormula))(1), nil), pr7)
    val pr9:Provable = interpret(nil <(nil, existsR("(1/v)^(1/2)".asTerm)(1), nil), pr8)
    val pr10:Provable = interpret(nil <(nil, dI()(1), nil), pr9)
    val pr11:Provable = interpret(nil <(nil, ODE(1)), pr10)
    //val pr12:Provable = interpret(ODE(1), pr11)
    pr11
  }

  //@TODO: Add stuff from vector proof
  def quad1Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, yInit: Term, theta1: Number, deltaTheta: Number):Provable = {
    println("Proving Quadrant 1 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val x0 = p1._1
    val y0 = p1._2
    val xEnd = p2._1
    val yEnd = p2._2
    //unfold ;
    val pr1 = interpret(dC(s"dx^2+dy^2=1".asFormula)(1) <(nil, dI()(1)), pr)
    val pr2 = interpret(dC(s"dx=(y-($cy))/($r)".asFormula)(1) <(nil, dI()(1)), pr1)
    val pr3 = interpret(dC(s"dy=-(x-($cx))/($r)".asFormula)(1) <(nil, dI()(1)), pr2)
    val pr4= interpret(dC(s"(($cx) - x)^2   + (($cy) - y)^2   = ($r)^2".asFormula)(1) <(nil, ODE(1)), pr3)
    //val pr3b =interpret(dC(s"(($cx) - ($xEnd))^2 + (($cy) - ($yEnd))^2 = ($r)^2".asFormula)(1) <(nil, ODE(1)), pr3a)
    val pr5 = interpret(dC(s"v^2=($v0)^2+2*($y0)-2*y".asFormula)(1) <(nil, dI()(1)), pr4)
    val pr6 = interpret(dC(s"v>0 ".asFormula)(1) <(nil, ODE(1)), pr5)
    pr6
  }
  
  def quad3Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, yInit: Term, theta1: Number, deltaTheta: Number):Provable = {
    println("Proving Quadrant 3 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    val pr1 = interpret(dC(s"dx=-(($cy)-y)/($r)".asFormula)(1)  <(nil, dI()(1)), pr)
    val pr2 = interpret(dC(s"dy=(($cx)-x)/($r)".asFormula)(1)  <(nil, dI()(1)), pr1)
    val pr3 = interpret(dC(s"v^2=($v0)^2+2*($y0)-2*y".asFormula)(1)  <(nil, dI()(1)), pr2)
    val pr4 = interpret(dC(s"v>0".asFormula)(1)  <(nil, ODE(1)), pr3)
    val pr5 = interpret(dC(s"y < ($cy)".asFormula)(1)  <(nil, dI()(1)), pr4)
    pr5
    //interpret(e, pr)
  }
  
  def quad4Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, yInit: Term, theta1: Number, deltaTheta: Number):Provable = {
    println("Proving Quadrant 4 Arc: " , p1,p2,bl,tr,v0,theta1,deltaTheta)
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    //val pr0 = interpret(implyR(1), pr)
    val pr1 = interpret(dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)), pr)
    val pr2 = interpret(dC(s"dy=(x-($cx))/($r)".asFormula)( 1)  <(nil, ODE(1)), pr1)
    val pr3 = interpret(dC(s"($cx)<=x".asFormula)(1)  <(nil, ODE(1)), pr2)
    val pr4 = interpret(dC(s"v^2=($v0)^2+2*($y0)-2*y".asFormula)(1) <(nil, ODE(1)), pr3)
    val pr5 = interpret(dC(s"(($cx)-x)^2+(($cy)-y)^2=($r)^2".asFormula)(1) <(nil, ODE(1)), pr4)
    val pr6 = interpret(dC(s"y < ($cy)".asFormula)(1) <(nil,
      dC(s"2*(y-($cy))*($r)!=0".asFormula)(1)  <(
        dG(s"{a'=(($cx)-x)*v/(2*(y-($cy))*($r))*a+0}".asDifferentialProgram, Some(s"a^2*(y-($cy))=-1".asFormula))(1) &
          existsR(s"(-1/(y-($cy)))^(1/2)".asTerm)(1) &
          ODE(1),
        ODE(1)
      )
    ), pr5)
    val pr7 = interpret(dC(s"v>0".asFormula)(1)  <(nil,
      dC(s"2*v*($r)!=0".asFormula)(1)  <(
        dG(s"{a'=(x-($cx))/(2*v*($r))*a+0}".asDifferentialProgram, Some("v>0".asFormula))(1) &
          existsR("(1/v)^(1/2)".asTerm)(1) &
          dC("a^2*v=1".asFormula)(1)  <(
            ODE(1),
            ODE(1)
          ),
        ODE(1)
      )
    ), pr6)
    pr7
  }

  def proveLineArith(pr: Provable, bl:TPoint, tr:TPoint, iSection:Int, nSections:Int):Provable = {
    val (hideYDefs, nYs) = {
      val js = List.tabulate(nSections)(j => j + 2).filter(j => !(j == iSection + 2 || j == iSection + 1))
      val e = js.map(i => hideL(-i)).foldLeft(nil)((acc, e) => e & acc)
      (e, nSections - js.length)
    }
    // J(0), y1 = _, ..., yn = _ |- \forall t t>= 0 ->(\forall s in [0,t] DC(s)) -> J(t)
    val pr1 = interpret(hideYDefs, pr)
    // J(0), yi |- " "
    val pr2 = interpret(andL(-1), pr1)
    val unpackPosts = andL('Llast)*(nSections - 1)
    // yi=_, global(0), &_j in sections{bound_j(0) -> post_j(0)} |- " "
    val pr3 = interpret(unpackPosts, pr2)
    val Jstart = 2 + nYs
    val hideJs = {
      val js = List.tabulate(nSections)(j => j + Jstart).filter(j => j != Jstart + iSection)
      js.map(i => hideL(-i)).foldLeft(nil)((acc, e) => e & acc)
    }
    // yi=_, global(0), (op,)_j in sections{bound_j(0) -> post_j(0)} |- " "
    val pr4 = interpret(hideJs, pr3)
    // yi=_, global(0), (bound_i(0) -> post_i(0)) |- \forall t  t>= 0 -> (\forall s in [0,t] DC(s)) -> J(t)
    val pr5 = interpret(allR(1) & implyR(1) & implyR(1), pr4)
    // yi=_, global(0), (bound_i(0) -> post_i(0)), t >= 0, (\forall s in [0,t] DC) |- J(t)
    val pr6 = interpret(implyL(-Jstart) <((hideL(-1)*(nYs+1)) & hideR(1) & QE, nil), pr5)
    val proveGlobal = QE
    // yi=_, global(0), post_i(0), t>= 0, (\forall s in [0,t] DC) |- (global(t) & (&_j in sections{bound_j(t) -> post_j(t)})
    val pr7 = interpret(andR(1) <(proveGlobal, nil) , pr6)
    val dcPos = Jstart + 2
    def coHideL(i : Int, pr:Provable) = {
      val anteSize = pr.subgoals.head.ante.length
      List.tabulate(anteSize)(j => j + 1).filter(j => j != i).map(j => hideL(-j)).foldLeft(nil)((acc,e) => e & acc)
    }
    // yi=_, global(0), post_i(0), t>= 0, (\forall s in [0,t] DC) |- (&_j in sections{bound_j(t) -> post_j(t)}
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
    // yi=_, global(0), post_i(0), t>= 0, DC(t) |- (&_j in sections{bound_j(t) -> post_j(t)}
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
    val pr9 = proveConjs(provePost, pr8, nSections-1)
    pr9
  }

  def sectionTactic(pr: Provable, p1: TPoint, p2: TPoint, v0:Number, yInit:Term, section: Section, iSection:Int, nSections: Int):Provable = {
    section match {
      case ArcSection(Some(param@ArcParam(bl,tr,theta1,deltaTheta)),Some(grad)) => {
        val (t1, t2) = (theta1.value, param.theta2.value)
        val q3 = t1 <= -90 && t2 <= -90
        val q4 = t1 >= -90 && t1 <= 0   && t2 <= 0
        val q1 = t1 >= 0   && t1 <= 90  && t2 <= 90
        val x = 1 + 1
        val pr1 =
          (q3, q4, q1) match {
            case (true, false, false) => quad3Tactic(pr, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta) // Quadrant 3
            case (false, true, false) => quad4Tactic(pr, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta) // Quadrant 4
            case (false, false, true) => quad1Tactic(pr, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta) // Quadrant 1
            case (false,false,false)  => quad2Tactic(pr, p1, p2, bl, tr, v0, yInit, theta1, deltaTheta) // Quadrant 2
            case _ => ???
          }
        interpret(dW(1) & QE, pr1)
      }
      case LineSection(Some(LineParam(bl,tr)), Some(grad)) =>
        println("Proving Line Segment: " , bl,tr)
        // @TODO: I am being bad and braking all the abstractions ever
        val t = Variable("kyxtime")
        val prSolved = interpret(solve(1), pr)
        proveLineArith(prSolved, bl, tr, iSection, nSections)
        /*val pr1 = interpret(AxiomaticODESolver.addTimeVar(1), pr)
        val pr1a = interpret(assignb(1), pr1)
        val pr2 = interpret(dC(s"v = old(v) - dy*($t)".asFormula)(1) <(nil, dI()(1)), pr1a)
        //val pr3 = interpret(dC(s"y = old(y) + dy*($t)".asFormula)(1) <(nil, dI()(1)), pr2)
        val pr3 = interpret(dC(s"y = old(y) + dy*(old(v)*($t) - dy*($t)^2/2)".asFormula)(1) <(nil, dI()(1)), pr2)
        val pr4 = interpret(dC(s"x = old(x) + dx*(old(v)*($t) - dy*($t)^2/2)".asFormula)(1) <(nil, dI()(1)), pr3)*/
        // @TODO: figure out why alignment between components is bad
        // @TODO: get the arithmetic to be faster
        //val pr5 = interpret(DebuggingTactics.debug("This QE is false", doPrint = true) & master(), prSolved)
        //pr5
      case _ => ???
    }
  }

  def provePosts(pr:Provable, fml:Formula, p1: TPoint, p2: TPoint, section: Section, v: Number, yInit: Term, i: Int, j:Int, nSections:Int):BelleExpr = {
    val thisE =
      if(i == j) {
        sectionTactic(pr, p1, p2, v, yInit,section, i, nSections)
        //@TODO: fix
        nil
      } else {
        dW(1) & QE
      }
    fml match {
      case And(p,q) => andR(1) <(thisE, provePosts(pr, q, p1, p2, section, v, yInit,i, j+1, nSections))
      case _ => thisE
    }
  }

  def componentTactic(pr:Provable, p1: TPoint, p2: TPoint, section: Section, v: Number, yInit: Term, i: Int, nSections:Int):Provable = {
    sectionTactic(pr, p1, p2, v, yInit, section, i, nSections)
  /*  val globalPost = ???
    val componentPost = provePosts(pr, pr.conclusion.succ.head, p1, p2, section, v, i, 0)
    andR(1) <(globalPost, componentPost)*/
  }

  def proveAllComponents(global:Provable, locals: List[Provable], points: List[(Term, Term)], segments: List[Section], v: Number, yInit: Term, i: Int, nSections: Int):Provable = {
    (points, segments, locals) match {
      case (p1 :: p2 :: Nil, s1 :: Nil, pr :: Nil) => componentTactic(pr, p1, p2, s1, v, yInit, i, nSections)
      case (p1 :: p2 :: ps, s1 :: ss, pr :: prs) =>
        val sg = componentTactic(pr, p1, p2, s1, v, yInit, i, nSections)
        proveAllComponents(global(sg, 0), prs, p2::ps, ss, v, yInit, i+1, nSections)
      case _ => ???
    }
  }

  def splitComponents(pr:Provable,i:Int = 0):(Provable, List[Provable]) = {
    pr.subgoals.head.succ.head match {
      case (Box(Choice(_,_), _)) =>
        //@TODO: Split off separate provable and merge back in
        val pr1 = interpret(choiceb(1) & andR(1), pr)
        val sgHead = Provable.startProof(pr1.subgoals(0))
        val sgTail = Provable.startProof(pr1.subgoals(1))
        val (global, locals) = splitComponents(sgTail, i+1)
        (pr1(global,1), sgHead::locals)
      case  _ =>
        (pr, Provable.startProof(pr.subgoals.last) :: Nil)
//      case Nil => ???
    }
  }

  def apply(fileName:String):Provable = {
    val parsed = CoasterXParser.parseFile(fileName).get
    val align@(aligned@(points, segments, v0, _), segmentDefs) = prepareFile(parsed)
    val spec = fromAligned(align)
    val pr = Provable.startProof(spec)
    val pr1 = interpret(implyR(1), pr)
    val pr2 = interpret(loop(invariant(align))(1), pr1)
    val pr3 = interpret(nil <(QE, nil, nil), pr2)
    val pr4 = interpret(nil <(QE, nil), pr3)
    val (globalPr, localPrs) = splitComponents(pr4)
      //mapChoices(es)
    val prEnd = proveAllComponents(globalPr, localPrs, points, segments.tail, v0, points.head._2, 0, segments.tail.length)
    //val prs = localPrs.zip(es)
    //val prEnd = interpret(e, pr4)
    assert(prEnd.isProved, "CoasterX model not proved")
    prEnd
  }
}
