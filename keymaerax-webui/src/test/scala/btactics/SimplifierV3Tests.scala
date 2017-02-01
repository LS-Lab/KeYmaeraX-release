package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable._

/**
  * Created by yongkiat on 12/19/16.
  */
class SimplifierV3Tests extends TacticTestBase {

  "SimplifierV3" should "simplify repeated propositions under context" in withMathematica { qeTool =>
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

  "SimplifierV3" should "do dependent arithmetic simplification" in withMathematica { qeTool =>
    val fml = "ar > 0 -> (x - 0 + 0 * y + 0 + 0/ar >= 0 - k)".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals should contain only
      Sequent(IndexedSeq(), IndexedSeq("ar>0->x>=-k".asFormula))
  }

  "SimplifierV3" should "do full sequent simplification" in withMathematica { qeTool =>
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
    pr.subgoals should contain only
      Sequent(
        IndexedSeq("x>=-k".asFormula,"ar>0".asFormula,"x*y=z+y".asFormula,"dhd-(a*t_+dho)=0".asFormula),
        IndexedSeq("P_()|Q_()|Q()".asFormula,"P_()|Q_()|Q()".asFormula,"true".asFormula)
      )

    //If ground arithmetic simplification is desired, it can be mixed in
//    val pr2 = proveBy(Sequent(antes,succs),fullSimpTac(taxs=composeIndex(arithGroundIndex,defaultTaxs)))
//    pr2.subgoals should contain only
//      Sequent(
//        IndexedSeq("x>=-k".asFormula,"ar>0".asFormula,"x*y=z+y".asFormula,"dhd-(a*t_+dho)=0".asFormula),
//        IndexedSeq("P_()|Q_()|Q()".asFormula,"P_()|Q_()|Q()".asFormula,"true".asFormula)
//      )
  }

  "SimplifierV3" should "search for close heuristics" in withMathematica { qeTool =>
    val fml = " 0 > x -> x <= 0 & y = 0 & z<x -> x != y+z | x >= 5 -> 5 < x | (x !=5 -> 5<x ) & a = 0 & y = z+a+b & a+z+b = y".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals.head.succ should contain only "0>x->y=0&z < x->x!=y+z|x>=5->5 < x|!x!=5&a=0&y=z+a+b&a+z+b=y".asFormula
  }

  "SimplifierV3" should "allow controlled custom rewrites" in withMathematica { qeTool =>
    //Force any =0s to be rewritten
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,TactixLibrary.QE)
    //Get rid of deMorgan once
    val custom2 = DerivedAxioms.notNotEqual.fact

    val fml = " 0 > x -> x <= 0 & y = 0 & z<x -> x != y+z | x >= 5 -> 5 < x | (x !=5 -> 5<x ) & a = 0 & y = z+a+b & a+z+b = y".asFormula
    val result = proveBy(fml,
      //Note: needs to simplify twice because the rewrites are not applied to exhaustion
      // (maybe that should be the default?)
      SimplifierV3.simpTac(List(custom1,custom2))(1) &
      SimplifierV3.simpTac(List(custom1,custom2))(1))

    result.subgoals.head.succ should contain only "0>x->y=0&z < x->5 < x|x=5&a=0&0=z+b".asFormula
  }

  it should "simplify terms under quantifiers" in withMathematica { qeTool =>
    val fml = "(\\forall t \\forall s \\forall y (t>=0 & 0 <= s & s<=t & y>0-> x=v_0*(0+1*t-0) -> x >= 0/y))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula, "v_0=5".asFormula)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), SimplifierV3.simpTac()(1))

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only("x_0=0".asFormula, "v_0=5".asFormula)
    result.subgoals.head.succ should contain only "\\forall t \\forall s \\forall y  (t>=0&0<=s&s<=t&y>0->x=v_0*t->x>=0)".asFormula
  }

  it should "handle existentials" in withMathematica { qeTool =>
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,TactixLibrary.QE)
    val fml = "\\exists y (y = 0 -> y-x = 0)".asFormula
    val ctxt = IndexedSeq("x=0".asFormula)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), SimplifierV3.simpTac(List(custom1))(1) & TactixLibrary.close)

    result shouldBe 'proved
  }

  it should "handle modalities (poorly) " in withMathematica { qeTool =>
    //note: k=0 is constant across the diamond, but it is difficult to keep around
    val custom1 = proveBy("F_() = 0 -> (F_() = 0)".asFormula,TactixLibrary.QE)
    val fml = "<{x_'=v&q(x_)}>(z = 0 -> x_' * y + z >= x' + k) & [{x_'=v&q(x_)}](z = 0 -> x_' * y + z >= x' + k)".asFormula
    val ctxt = IndexedSeq("k=0".asFormula)
    val result = proveBy(Sequent(ctxt, IndexedSeq(fml)), SimplifierV3.simpTac(List(custom1))(1))

    result.subgoals should have size 1
    result.subgoals.head.ante should contain only("k=0".asFormula)
    result.subgoals.head.succ should contain only "<{x_'=v&q(x_)}>(z=0->x_'*y>=x'+k) & [{x_'=v&q(x_)}](z=0->x_'*y>=x'+k)".asFormula
  }

  it should "handle equiv and not " in withMathematica { qeTool =>
    val fml = "!!!!!!!!!!P() <-> !!!!!!!!!!!P()".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))

    result.subgoals should have size 1
    result.subgoals.head.succ should contain only "P() <-> !P()".asFormula
  }

  it should "avoid unification pitfalls" in withMathematica { qeTool =>

    //The indexes support using Scala externally (outside the unifier) to specify when a rewrite applies
    //The following rewrite works badly with the first simplifier (because of a bad unification)
    //In general, a rewrite with repeated symbols should probably be checked externally using this mechanism to be safe
    val rw = proveBy("F_() - F_() = 0".asFormula, TactixLibrary.QE)
    val minus = ( (t:Term,ctx:context) =>
      t match {
        case Minus(l, r) if l == r => List(rw)
        case _ => List()
      }
    )
    val fml = "(F_() - G_()) - (H_() - H_()) + (Z_()-Z_()) = F_() - G_()".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac(taxs = composeIndex(minus,defaultTaxs))(1))

    result.subgoals should have size 1
    result.subgoals.head.succ should contain only "true".asFormula
  }

  it should "simplify ACAS X goal" in withMathematica { qeTool =>
    val minusSimp1 = proveBy("F_() + G_() - G_() = F_()".asFormula,TactixLibrary.QE)
    val minusSimp2 = proveBy("F_() - G_() + G_() = F_()".asFormula,TactixLibrary.QE)

    val minus = ( (t:Term,ctx:context) =>
      t match {
        case Minus(Plus(a,b), c) if b == c => List(minusSimp1)
        case Plus(Minus(a,b),c) if b == c => List(minusSimp2)
        case _ => List()
      }
      )
    val fml = ("0<=t_+t&t_+t < max((0,d))&dhf*(t_+t-max((0,d)))-w*max((0,w*(dhf-(-w*ad*max((0,d))+dho))))^2/(2*ar)+(-w*ad/2*max((0,d))^2+dho*max((0,d)))=-w*ad/2*(t_+t)^2+dho*(t_+t)|dhf*(t_+t-max((0,d)))=dhf*(t_+t-max((0,d)))-w*max((0,w*(dhf-(-w*ad*max((0,d))+dho))))^2/(2*ar)+w*max((0,w*(dhf-(-w*ad*max((0,d))+dho))))^2/(2*ar)->abs(r-rv*(t_+t))>rp|w*(h-(dhf*(t_+t-max((0,d)))-w*max((0,w*(dhf-(-w*ad*max((0,d))+dho))))^2/(2*ar)+(-w*ad/2*max((0,d))^2+dho*max((0,d))))) < -hp").asFormula
    val result = proveBy(fml, SimplifierV3.simpTac(taxs = composeIndex(minus,defaultTaxs))(1))
    println(result)
  }

  it should "simplify sole function arguments" in withMathematica { tool =>
    val fml = "abs(0*1+0)>=0".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))

    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "abs(0)>=0".asFormula
  }


  it should "simplify multiple function arguments" in withMathematica { tool =>
    val fml = "max(0*1+0, 0+1*y-0)>=0".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "max(0,y)>=0".asFormula
  }

  it should "not choke on noarg functions" in withMathematica { tool =>
    val fml = "f()>=0".asFormula
    val result = proveBy(fml, SimplifierV3.simpTac()(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "f()>=0".asFormula
  }

  it should "simplify terms" in withMathematica { qeTool =>
    val fml = "(\\forall t \\forall s (t>=0 & 0 <= s & s<=t -> x=v_0*(0+1*t-0) -> x >= 5))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=5".asFormula)
    val tactic = simpTac()
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=5".asFormula)
    result.subgoals.head.succ should contain only "\\forall t \\forall s (t>=0&0<=s&s<=t->x=v_0*t->x>=5)".asFormula
  }

  it should "simplify terms when applied to term position" in withMathematica { qeTool =>
    val fml = "x=v_0*(0+1*t-0) -> x >= 0".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac()
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1,PosInExpr(0::1::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=0".asFormula)
    result.subgoals.head.succ should contain only "x=v_0*t -> x>=0".asFormula
  }

  it should "simplify in multi-arg formula and term positions with arbitrary nesting" in withMathematica { qeTool =>
    val fml = "P( f(x+0,y,(0*z+0,a+0),b-0,c), k,(f(x+0,y,0*z+0,(a+0,b-0,c)),f(x+0,(y,0*z+0),a+0,(b-0,c))), (a,f(x+0,(y,0*z+0,a+0,b-0),c)))".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac()
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals.head.succ should contain only "P((f((x,(y,((0,a),(b,c))))),(k,((f((x,(y,(0,(a,(b,c)))))),f((x,((y,0),(a,(b,c)))))),(a,f((x,((y,(0,(a,b))),c))))))))".asFormula

  }

  it should "support equality rewriting" in withMathematica { qeTool =>
    //Note: this is probably pretty costly, so off by default
    val fml = "\\forall t (t = 0 -> (\\forall s (s = 1 -> \\forall r (r = 5 -> \\forall q (q = 0 -> r*s+t+a+b+t*r+q<=5+q+r+t+s+r+a+b)))))".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac(taxs=composeIndex(groundEqualityIndex,defaultTaxs))
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    //todo: might benefit from AC rewriting
    result.subgoals.head.succ should contain only "\\forall t (t=0->\\forall s (s=1->\\forall r (r=5->\\forall q (q=0->5+a+b<=16+a+b))))".asFormula
  }
}
