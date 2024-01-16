/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._

import scala.collection.immutable._
import org.scalatest.LoneElement._
import testHelper.KeYmaeraXTestTags.TodoTest

/**
  * Created by yongkiat on 12/19/16.
  */
class SimplifierV3Tests extends TacticTestBase {

  "SimplifierV3" should "simplify repeated propositions under context" in withMathematica { _ =>
    val fml = "R() -> P() & Q() -> P() & (R() & P()) & Q() & (R() & P() & Z() & Y())".asFormula
    val ctxt = IndexedSeq("Y()".asFormula)
    val tactic = SimplifierV3.simpTac()
    //Top level simplification at different succedents
    proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1)).subgoals should contain only
      Sequent(ctxt, IndexedSeq("R()->P()&Q()->Z()".asFormula))
    proveBy(Sequent(ctxt,IndexedSeq(fml,fml,fml)), tactic(2)).subgoals should contain only
      Sequent(ctxt, IndexedSeq("R()->P()&Q()->P()&(R()&P())&Q()&R()&P()&Z()&Y()".asFormula, "R()->P()&Q()->Z()".asFormula, "R()->P()&Q()->P()&(R()&P())&Q()&R()&P()&Z()&Y()".asFormula))
    //Inner simplification
    proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1,PosInExpr(1::1::Nil))).subgoals should contain only
      Sequent(ctxt, IndexedSeq("R()->P()&Q()->P()&R()&Q()&Z()&Y()".asFormula))
    proveBy(Sequent(ctxt,IndexedSeq(fml,fml,fml)), tactic(3,PosInExpr(1::1::Nil))).subgoals should contain only
      Sequent(ctxt, IndexedSeq("R()->P()&Q()->P()&(R()&P())&Q()&R()&P()&Z()&Y()".asFormula, "R()->P()&Q()->P()&(R()&P())&Q()&R()&P()&Z()&Y()".asFormula, "R()->P()&Q()->P()&R()&Q()&Z()&Y()".asFormula))
  }

  it should "simplify propositional" in withTactics {
    proveBy("!p(), !q(), r()&p() | r()&q() ==>".asSequent, SimplifierV3.fullSimplify & TactixLibrary.closeF) shouldBe Symbol("proved")
    proveBy("r()&p() | r()&q(), !p(), !q() ==>".asSequent, SimplifierV3.fullSimplify & TactixLibrary.closeF) shouldBe Symbol("proved")
    proveBy("!p(), r()&p() | r()&q(), !q() ==>".asSequent, SimplifierV3.fullSimplify & TactixLibrary.closeF) shouldBe Symbol("proved")
  }

  it should "do beautification simplification" in withMathematica { _ =>
    val fml = "x>0 & z>=y -> x^(-1)*((-1)*y+z) >= 0".asFormula
    proveBy(fml, SimplifierV3.simplify(1)).subgoals.loneElement shouldBe "==> x>0 & z>=y -> (z-y)/x >= 0".asSequent
  }

  it should "keep rational constants" in withMathematica { _ =>
    val fml = "1/2*x^2 >= 0".asFormula
    proveBy(fml, SimplifierV3.simplify(1)).subgoals.loneElement shouldBe "==> 1/2*x^2 >= 0".asSequent
  }

  it should "do dependent arithmetic simplification" in withMathematica { _ =>
    val fml = "ar > 0 -> (x - 0 + 0 * y + 0 + 0/ar >= 0 - k)".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals.loneElement shouldBe "==> ar>0->x>=-k".asSequent
  }

  it should "do full sequent simplification" in withMathematica { _ =>
    val antes = IndexedSeq(
      "(x - 0 + 0 * y + 0 + 0/ar >= 0 - k)".asFormula,
      "ar>0".asFormula,
      "x * y = z + y + 0 - 0^2".asFormula,
      "dhd-(a*t_+dho)=(-w*ad)*0".asFormula
    )
    val succs = IndexedSeq(
      "P_() | Q_() & ar >0 | P_() | Q()".asFormula,
      "P_() | Q_() & ar >0 | P_() | Q()".asFormula,
      "dhd-(a*t_+dho)=-w*ad*0".asFormula
    )
    //todo: A 'not' like mechanism to simplify across multiple succedents?
    val pr = proveBy(Sequent(antes,succs),fullSimpTac())
    pr.subgoals.loneElement shouldBe "x>=-k, ar>0, x*y=z+y, dhd-(a*t_+dho)=0 ==> P_()|Q_()|Q(), P_()|Q_()|Q(), true".asSequent

    //If ground arithmetic simplification is desired, it can be mixed in
//    val pr2 = proveBy(Sequent(antes,succs),fullSimpTac(taxs=composeIndex(arithGroundIndex,defaultTaxs)))
//    pr2.subgoals should contain only
//      Sequent(
//        IndexedSeq("x>=-k".asFormula,"ar>0".asFormula,"x*y=z+y".asFormula,"dhd-(a*t_+dho)=0".asFormula),
//        IndexedSeq("P_()|Q_()|Q()".asFormula,"P_()|Q_()|Q()".asFormula,"true".asFormula)
//      )
  }

  it should "hide resulting true, false" in withMathematica { _ =>
    val fml = "x>=0, x=0 ==> x<0".asSequent
    proveBy(fml, SimplifierV3.fullSimpTac()).subgoals.loneElement shouldBe "x=0 ==> ".asSequent
  }

  it should "search for close heuristics" in withMathematica { _ =>
    val fml = " 0 > x -> x <= 0 & y = 0 & z<x -> x != y+z | x >= 5 -> 5 < x | (x !=5 -> 5<x ) & a = 0 & y = z+a+b & a+z+b = y".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals.loneElement shouldBe "==> 0>x->y=0&z < x->x!=y+z|x>=5->5 < x|!x!=5&a=0&y=z+a+b&a+z+b=y".asSequent
  }

  it should "allow controlled custom rewrites" in withMathematica { _ =>
    //Force any =0s to be rewritten
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,TactixLibrary.QE)
    //Get rid of deMorgan once
    val custom2 = Ax.notNotEqual.provable

    val fml = " 0 > x -> x <= 0 & y = 0 & z<x -> x != y+z | x >= 5 -> 5 < x | (x !=5 -> 5<x ) & a = 0 & y = z+a+b & a+z+b = y".asFormula
    val result = proveBy(fml,
      //Note: needs to simplify twice because the rewrites are not applied to exhaustion
      // (maybe that should be the default?)
      SimplifierV3.simpTac(List(custom1,custom2))(1) &
      SimplifierV3.simpTac(List(custom1,custom2))(1))

    result.subgoals.head.succ should contain only "0>x->y=0&z < x->5 < x|x=5&a=0&0=z+b".asFormula
  }

  it should "simplify negated multiplication" in withMathematica { _ =>
    SimplifierV3.termSimp("-1*x".asTerm, Set.empty, SimplifierV3.defaultTaxs)._1 shouldBe "-x".asTerm
    SimplifierV3.termSimp("-(1*x)".asTerm, Set.empty, SimplifierV3.defaultTaxs)._1 shouldBe "-x".asTerm
    SimplifierV3.termSimp("(-1)*x".asTerm, Set.empty, SimplifierV3.defaultTaxs)._1 shouldBe "-x".asTerm
    SimplifierV3.termSimp("-(1)*x".asTerm, Set.empty, SimplifierV3.defaultTaxs)._1 shouldBe "-x".asTerm
  }

  it should "FEATURE_REQUEST: saturate term simplifiers" taggedAs TodoTest in withMathematica { _ =>
    SimplifierV3.termSimp("0-(x-y)".asTerm, Set.empty, SimplifierV3.defaultTaxs)._1 shouldBe "y-x".asTerm
  }

  it should "simplify plus negation" in withMathematica { _ =>
    SimplifierV3.termSimp("x+(-y)".asTerm, Set.empty, SimplifierV3.defaultTaxs)._1 shouldBe "x-y".asTerm
  }

  it should "simplify terms under quantifiers" in withMathematica { _ =>
    val fml = "(\\forall t \\forall s \\forall y (t>=0 & 0 <= s & s<=t & y>0-> x=v_0*(0+1*t-0) -> x >= 0/y))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula, "v_0=5".asFormula)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), SimplifierV3.simpTac()(1))

    result.subgoals.loneElement shouldBe "x_0=0, v_0=5 ==> \\forall t \\forall s \\forall y (t>=0&0<=s&s<=t&y>0->x=v_0*t->x>=0)".asSequent
  }

  it should "handle existentials" in withMathematica { _ =>
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,TactixLibrary.QE)
    val fml = "\\exists y (y = 0 -> y-x = 0)".asFormula
    val ctxt = IndexedSeq("x=0".asFormula)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), SimplifierV3.simpTac(List(custom1))(1) & TactixLibrary.close)
    result shouldBe Symbol("proved")
  }

  it should "handle modalities (poorly) " in withMathematica { _ =>
    //note: k=0 is constant across the diamond, but it is difficult to keep around
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,TactixLibrary.QE)
    val fml = "<{x_'=v&q(x_)}>(z = 0 -> x_' * y + z >= x' + k) & [{x_'=v&q(x_)}](z = 0 -> x_' * y + z >= x' + k)".asFormula
    val ctxt = IndexedSeq("k=0".asFormula)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), SimplifierV3.simpTac(List(custom1))(1))
    result.subgoals.loneElement shouldBe "k=0 ==> <{x_'=v&q(x_)}>(z=0->x_'*y>=x'+k) & [{x_'=v&q(x_)}](z=0->x_'*y>=x'+k)".asSequent
  }

  it should "handle equiv and not " in withMathematica { _ =>
    val fml = "!!!!!!!!!!P() <-> !!!!!!!!!!!P()".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals.loneElement shouldBe "==> P() <-> !P()".asSequent
  }

  it should "avoid unification pitfalls" in withMathematica { _ =>

    //The indexes support using Scala externally (outside the unifier) to specify when a rewrite applies
    //The following rewrite works badly with the first simplifier (because of a bad unification)
    //In general, a rewrite with repeated symbols should probably be checked externally using this mechanism to be safe
    val rw = proveBy("F_() - F_() = 0".asFormula, TactixLibrary.QE)
    val minus = (t: Term, _: context) => t match {
      case Minus(l, r) if l == r => List(rw)
      case _ => List()
    }
    val fml = "(F_() - G_()) - (H_() - H_()) + (Z_()-Z_()) = F_() - G_()".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac(taxs = composeIndex(minus,defaultTaxs))(1))

    result.subgoals.loneElement shouldBe "==> true".asSequent
  }

  it should "simplify sole function arguments" in withMathematica { _ =>
    val fml = "abs(0*1+0)>=0".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))

    result.subgoals.loneElement shouldBe "==> abs(0)>=0".asSequent
  }


  it should "simplify multiple function arguments" in withMathematica { _ =>
    val fml = "max(0*1+0, 0+1*y-0)>=0".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals.loneElement shouldBe "==> max(0,y)>=0".asSequent
  }

  it should "not choke on noarg functions" in withMathematica { _ =>
    val fml = "f()>=0".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals.loneElement shouldBe "==> f()>=0".asSequent
  }

  it should "simplify terms" in withMathematica { _ =>
    val fml = "(\\forall t \\forall s (t>=0 & 0 <= s & s<=t -> x=v_0*(0+1*t-0) -> x >= 5))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=5".asFormula)
    val tactic = simpTac()
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "x_0=0, v_0=5 ==> \\forall t \\forall s (t>=0&0<=s&s<=t->x=v_0*t->x>=5)".asSequent
  }

  it should "simplify terms when applied to term position" in withMathematica { _ =>
    val fml = "x=v_0*(0+1*t-0) -> x >= 0".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac()
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1,PosInExpr(0::1::Nil)))
    result.subgoals.loneElement shouldBe "x_0=0, v_0=0 ==> x=v_0*t -> x>=0".asSequent
  }

  it should "simplify in multi-arg formula and term positions with arbitrary nesting" in withMathematica { _ =>
    val fml = "P( f(x+0,y,(0*z+0,a+0),b-0,c), k,(f(x+0,y,0*z+0,(a+0,b-0,c)),f(x+0,(y,0*z+0),a+0,(b-0,c))), (a,f(x+0,(y,0*z+0,a+0,b-0),c)))".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac()
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==> P((f((x,(y,((0,a),(b,c))))),(k,((f((x,(y,(0,(a,(b,c)))))),f((x,((y,0),(a,(b,c)))))),(a,f((x,((y,(0,(a,b))),c))))))))".asSequent

  }

  it should "support equality rewriting" in withMathematica { _ =>
    //Note: this is probably pretty costly, so off by default
    val fml = "\\forall t (t = 0 -> (\\forall s (1 = s -> \\forall r (r = 5+s -> \\forall q (t+r = q -> r*s+t+a+b+t*r+q<=5+q+r+t+s+r+a+b)))))".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    //todo: might benefit from AC rewriting
    result.subgoals.loneElement shouldBe "==> \\forall t (t=0->\\forall s (1=s->\\forall r (r=6->\\forall q (6=q->6+a+b+6<=24+a+b))))".asSequent
  }

  it should "handle weird conjunct orders" in withMathematica { _ =>
    val fml = "A() -> B() & (C() & D()) & (P() & Q()) & R() -> (R() & Q()) & P() & (C() & D()) & E() ".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(taxs = composeIndex(groundEqualityIndex, defaultTaxs))
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==> A()->B()&(C()&D())&(P()&Q())&R()->E()".asSequent
  }

  it should "handle duplicate conjuncts" in withMathematica { _ =>
    val fml = " (A() & B()) & C() -> (A() & B()) & C() -> (A() & B()) & C() -> B() & C() & A() & A() & D()".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(taxs = composeIndex(groundEqualityIndex, defaultTaxs))
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==> (A()&B())&C()->D()".asSequent
  }

  it should "skip over inexact decimal arithmetic" in withMathematica { _ =>
    val fml = "4*1.0-4.0/3 = -3.0/2 + 1/6 + (2 + 3) * 4.0".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac()
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==> 4-4/3=1/6-3/2+20".asSequent
  }

  it should "cooperate with chase" in withMathematica { _ =>
    val fml = "!(A = 5 | !3<=6 & B<=1 & C>=7 & !(D+B<=A+C | !(C+D<=F_() & G_()*5=8) | 100=1))".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(faxs = composeIndex(defaultFaxs,chaseIndex),taxs = emptyTaxs)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==>  A!=5&(3<=6|B>1|C < 7|D+B<=A+C|(C+D>F_()|G_()*5!=8)|100=1)".asSequent
  }

  it should "simplify FuncOf args" in withMathematica { _ =>
    val fml = "y=3 & v=5 & y=3  -> f((v,v,v),x,(y,z,(z,z),y))=1".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(faxs = composeIndex(defaultFaxs,chaseIndex),taxs = groundEqualityIndex)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==>  y=3&v=5->f(((5,(5,5)),(x,(3,(z,((z,z),3))))))=1".asSequent
  }

  it should "simplify PredOf args" in withMathematica { _ =>
    val fml = "y=3 & v=5 & y=3  -> P((v,v,v),x,(y,z,(z,z),y)) -> 1 = v".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(faxs = composeIndex(defaultFaxs,chaseIndex),taxs = groundEqualityIndex)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==>  y=3&v=5->P(((5,(5,5)),(x,(3,(z,((z,z),3))))))->1=5".asSequent
  }

  it should "allow full equality rewrites" in withMathematica { _ =>
    val fml = "\\forall v (v=5*x+3 -> p(v))".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(faxs = composeIndex(defaultFaxs,chaseIndex),taxs = fullEqualityIndex)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), tactic(1))
    result.subgoals.loneElement shouldBe "==>  \\forall v (v=5*x+3 -> p(5*x+3))".asSequent
  }

  it should "work in programs" in withMathematica { _ =>
    proveBy("==> [x:=1+0^3*x;]x>=0".asSequent, simpTac()(1, PosInExpr(0::1::Nil))).subgoals.
      loneElement shouldBe "==> [x:=1;]x>=0".asSequent
  }

  it should "FEATURE_REQUEST: work in ODEs" taggedAs TodoTest in withMathematica { _ =>
    proveBy("x>=0 ==> [{x'=1+0*y}]x>=0".asSequent, simpTac()(1, PosInExpr(0::0::1::Nil))).subgoals.
      loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
    //@todo x is bound in ODE and occurs free in 0*x and therefore clashes/CQ aborts
    proveBy("x>=0 ==> [{x'=1+0*x}]x>=0".asSequent, simpTac()(1, PosInExpr(0::0::1::Nil))).subgoals.
      loneElement shouldBe "x>=0 ==> [{x'=1}]x>=0".asSequent
  }

  it should "FEATURE_REQUEST: work in loops" taggedAs TodoTest in withMathematica { _ =>
    proveBy("x>=0 ==> [{x:=1+0*y;}*]x>=0".asSequent, simpTac()(1, PosInExpr(0::0::1::Nil))).subgoals.
      loneElement shouldBe "x>=0 ==> [{x:=1;}*]x>=0".asSequent
    //@todo x is bound in loop and occurs free in 0*x and therefore clashes/CQ aborts
    proveBy("x>=0 ==> [{x:=1+0*x;}*]x>=0".asSequent, simpTac()(1, PosInExpr(0::0::1::Nil))).subgoals.
      loneElement shouldBe "x>=0 ==> [{x:==1;}*]x>=0".asSequent
  }

  it should "not rewrite numbers" in withMathematica { _ =>
    proveBy("0=1 -> f(0,1)>=0".asFormula, SimplifierV3.simpTac(
      taxs = SimplifierV3.composeIndex(SimplifierV3.groundEqualityIndex, SimplifierV3.defaultTaxs),
      faxs = SimplifierV3.defaultFaxs
    )(1)).subgoals.loneElement shouldBe "==> 0=1 -> f(0,1)>=0".asSequent
  }

  it should "not fail when predicates unify with true/false of some simplification axioms" in withMathematica { _ =>
    //@note p(x) unifies with F_() and q(x) unifies with true in F_()->true, but applying substitution to F_()->true
    //      does not result in original p(x)->q(x)
    val s = "x>=0 -> (p(x)->q(x)), x>=0 ==> ".asSequent
    proveBy(s, SimplifierV3.simplify(-1)).subgoals.loneElement shouldBe "p(x) -> q(x), x>=0 ==> ".asSequent
  }

  "Normalizer" should "do some normalization" in withMathematica { _ =>
    val fml = "x*y=0 & (! x>=5 & y < 0 -> !(x>0 | 1+z>f+g+1.0))".asFormula

    //base normalizer only does NNF
    val baseres = baseNormalize(fml)

    //semialg normalizer forces everything to have 0 on RHS
    val semires = semiAlgNormalize(fml)

    // maxmin normalizer further turns everything into max/min/abs
    // It should be ran AFTER semiAlgNormalize.
    // Reason: we often want the intermediate result
    val maxminres = maxMinGeqNormalize(semires._1)

    baseres._1 shouldBe "x*y = 0 & ((x>=5|y>=0)|x<=0&1+z<=f+g+1.0)".asFormula

    semires._1 shouldBe "x*y = 0 & ((x-5>=0|y>=0)|0-x>=0&f+g+1.0-(1+z)>=0)".asFormula

    maxminres._1 shouldBe "min((-abs(x*y),max((max((x-5,y)),min((0-x,f+g+1.0-(1+z)))))))>=0".asFormula
  }

  it should "not fail on true/false" in withMathematica { _ =>
    semiAlgNormalize("true".asFormula)._1 shouldBe "0=0".asFormula
    semiAlgNormalize("false".asFormula)._1 shouldBe "1=0".asFormula
    semiAlgNormalize("true -> x>=5".asFormula)._1 shouldBe "1=0|x-5>=0".asFormula
    semiAlgNormalize("x>=5 -> false".asFormula)._1 shouldBe "5-x>0|1=0".asFormula
    semiAlgNormalize("!x>=5 -> false".asFormula)._1 shouldBe "x-5>=0|1=0".asFormula
    semiAlgNormalize("true <-> x>=5".asFormula)._1 shouldBe "(0=0&x-5>=0)|(1=0&5-x>0)".asFormula

    baseNormalize("false -> true".asFormula)._1 shouldBe "true|true".asFormula
    algNormalize("true -> x=4".asFormula)._1 shouldBe "1*(x-4)=0".asFormula
    maxMinGeqNormalize("false|x-5>=0".asFormula)._1 shouldBe "max(-1,x-5)>=0".asFormula
  }

  "simplify" should "find contradictions" in withMathematica { _ =>
    proveBy("x=1, x!=1 ==>".asSequent, simplify(-1)).subgoals.loneElement shouldBe "false, x!=1 ==>".asSequent
    proveBy("x=1, !x=1 ==>".asSequent, simplify(-1)).subgoals.loneElement shouldBe "false, !x=1 ==>".asSequent
  }

  "simplifyAllCtx" should "consider succedent when searching for contradictions" in withMathematica { _ =>
    proveBy("(x=1 | x=2) | x=3 ==> x=1 | x=2 | x=3".asSequent, simplifyAllCtx(-1)).subgoals.
      loneElement shouldBe "false, !x=3, !x=2, !x=1 ==>".asSequent
  }

  it should "simplify succedent" in withMathematica { _ =>
    proveBy("(x=1 & y=2) & z=3 ==> x=1 & y=2 & z=3".asSequent, simplifyAllCtx(1)).subgoals.
      loneElement shouldBe "z=3, x=1, y=2 ==> true".asSequent
  }

  it should "FEATURE_REQUEST: consider remaining succedent when simplifying a formula in the succedent" taggedAs TodoTest in withMathematica { _ =>
    proveBy("x=1 ==> x=1 & y=2, y!=2".asSequent, simplifyAllCtx(1)) shouldBe Symbol("proved")
  }

  it should "FEATURE_REQUEST: find contradictions hidden in double negations" taggedAs TodoTest in withMathematica { _ =>
    proveBy("x=1 ==> !x!=1".asSequent, simplifyAllCtx(-1)).subgoals.loneElement shouldBe "false, !!x!=1 ==>".asSequent
  }

}
