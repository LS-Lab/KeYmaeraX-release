package btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV2._
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._

/**
  * Created by yongkiat on 10/5/16.
  */
class SimplifierV2Tests extends TacticTestBase {

  "SimplifierV2" should "simplify repeated propositions under context" in withMathematica { qeTool =>
    val fml = "R() -> P() & Q() -> P() & (R() & P()) & Q() & (R() & P() & Z() & Y())".asFormula
    val ctxt = IndexedSeq("Y()".asFormula)
    val tactic = simpTac
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

  it should "simplify under quantifiers and modalities" in withMathematica { qeTool =>
    val fml = ("(\\forall x (P() & Q() & x = 0 & P() & Q())) & (\\exists y (P() & Q() & Q() & y = 5)) | " +
      "<{x_'=v&q(x_)}>(P() | P() & Q())").asFormula
    val ctxt = IndexedSeq("x=0".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "\\forall x (P()&Q()&x=0)&\\exists y (P()&Q()&y=5)|<{x_'=v&q(x_)}>P()".asFormula
  }

  it should "simplify terms" in withMathematica { qeTool =>
    val fml = "(\\forall t \\forall s (t>=0 & 0 <= s & s<=t -> x=v_0*(0+1*t-0) -> x >= 5))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=5".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=5".asFormula)
    result.subgoals.head.succ should contain only "\\forall t \\forall s (t>=0&0<=s&s<=t->x=5*t->x>=5)".asFormula
  }

  it should "simplify terms 2" in withMathematica { qeTool =>
    val fml = "(\\forall t \\forall s (t>=0 & 0 <= s & s<=t -> x=v_0*(0+1*t-0) -> x >= 0))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=0".asFormula)
    //@todo vacuous quantifier
    result.subgoals.head.succ should contain only "\\forall t \\forall s true".asFormula
  }

  it should "simplify terms when applied to term position" in withMathematica { qeTool =>
    val fml = "x=v_0*(0+1*t-0) -> x >= 0".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1,PosInExpr(0::1::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=0".asFormula)
    result.subgoals.head.succ should contain only "x=v_0*t -> x>=0".asFormula
  }

  it should "simplify program auxiliaries in loop" in withMathematica { qeTool =>
    //ETCS essentials:
    val fml = ("[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB")))
    pr shouldBe 'proved
    res shouldBe "[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=-b;++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=A;}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "simplify program auxiliaries with precondition" in withMathematica { qeTool =>
    //ETCS essentials:
    val fml = ("v^2<=2*b*(m-z)&b>0&A>=0->[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB")))
    pr shouldBe 'proved
    res shouldBe "v^2<=2*b*(m-z)&b>0&A>=0->[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=-b;++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=A;}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "simplify program auxiliaries with multiple preconditions" in withMathematica { qeTool =>
    val fml = ("a<=b & b<=c -> v^2<=2*b*(m-z)&b>0&A>=0->[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB")))
    pr shouldBe 'proved
    res shouldBe "a<=b&b<=c->v^2<=2*b*(m-z)&b>0&A>=0->[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=-b;++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=A;}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "leave open bad rewrites" in withMathematica { qeTool =>
    val fml = ("v^2<=2*b*(m-z)&b>0&A>=0->[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB"),Variable("a")))
    pr.isProved shouldBe false
    res shouldBe "v^2<=2*b*(m-z)&b>0&A>=0->[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "simplify sole function arguments" in withMathematica { tool =>
    val fml = "abs(0*1+0)>=0".asFormula
    val result = proveBy(fml, simpTac(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "abs(0)>=0".asFormula
  }

  it should "simplify multiple function arguments" in withMathematica { tool =>
    val fml = "max(0*1+0, 0+1*y-0)>=0".asFormula
    val result = proveBy(fml, simpTac(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "max(0,y)>=0".asFormula
  }

  it should "not choke on noarg functions" in withMathematica { tool =>
    val fml = "f()>=0".asFormula
    val result = proveBy(fml, simpTac(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "f()>=0".asFormula
  }

  it should "simplify in quantified" in withMathematica { tool =>
    val ante = IndexedSeq("x>0".asFormula)
    val succ = IndexedSeq("\\forall y (x>0&y>2)".asFormula)
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(1))
    result.subgoals.head.succ should contain only "\\forall y y>2".asFormula
  }

  it should "simplify in quantified 2" in withMathematica { tool =>
    val ante = IndexedSeq("x>0".asFormula, "y>3".asFormula)
    val succ = IndexedSeq("\\forall y (x>0&y>2)".asFormula)
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(1))
    result.subgoals.head.succ should contain only "\\forall y y>2".asFormula
  }

  it should "simplify in antecedent" in withMathematica { tool =>
    val ante = IndexedSeq("true -> x>0*y".asFormula)
    val succ = IndexedSeq()
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(-1))
    result.subgoals.head.ante should contain only "x>0".asFormula
  }

  it should "simplify in antecedent with context" in withMathematica { tool =>
    val ante = IndexedSeq("x>0".asFormula, "x>0 -> y>3".asFormula)
    val succ = IndexedSeq()
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(-2))
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>3".asFormula)
  }

  it should "simplify entire sequent (forwards)" in withMathematica { tool =>
    val ante = IndexedSeq("x>0".asFormula, "x>0 -> y>3".asFormula, "x>=0 -> y>4".asFormula, "x>0 -> y>5".asFormula,"5=z".asFormula)
    val succ = IndexedSeq("z>3".asFormula)
    val result = proveBy(Sequent(ante, succ), SimplifierV2.fullSimpTac)

    result.subgoals.head.succ should contain only ("5>3".asFormula)
  }

  it should "(attempt to) simplify ground terms" in withMathematica { tool =>
    val succ = "(1+2+3+4+5+6)^2/6-5-4-3-2*5 = 7".asFormula
    val result = proveBy(succ, SimplifierV2.simpTac(1))
    println(result)
  }

  it should "rewrite simple equalities" in withMathematica { tool =>
    val succ = "x+y+(x+y)+(x+y+z)".asTerm

    val fml = "x+y = 0 -> z =0 -> x+y+(x+y)+(x+y+z) = 0".asFormula
    val result = proveBy(fml, SimplifierV2.simpTac(1))

    result.subgoals.head.succ should contain only True

  }


  it should "search for close heuristics" in withMathematica { tool =>

    val fml = " x>0 -> x >= 0 & x != 0 & y < 5 & 5 > y & 5!= y | y!=5 & z = 5 & z != 5 & 5 = z".asFormula
    val result = proveBy(fml, SimplifierV2.simpTac(1))

    println(result)
//    result.subgoals.head.succ should contain only True

  }
}
