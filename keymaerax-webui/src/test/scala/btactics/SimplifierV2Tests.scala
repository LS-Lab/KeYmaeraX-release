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

  "SimplifierV2" should "simplify repeated propositions under context" in withQE { _ =>
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

  it should "simplify under quantifiers and modalities" in withQE { _ =>
    val fml = ("(\\forall x (P() & Q() & x = 0 & P() & Q())) & (\\exists y (P() & Q() & Q() & y = 5)) | " +
      "<{x_'=v&q(x_)}>(P() | P() & Q())").asFormula
    val ctxt = IndexedSeq("x=0".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x=0".asFormula
    result.subgoals.head.succ should contain only "\\forall x (P()&Q()&x=0)&\\exists y (P()&Q()&y=5)|<{x_'=v&q(x_)}>P()".asFormula
  }

  it should "simplify terms" in withQE { _ =>
    val fml = "(\\forall t \\forall s (t>=0 & 0 <= s & s<=t -> x=v_0*(0+1*t-0) -> x >= 5))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=5".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=5".asFormula)
    result.subgoals.head.succ should contain only "\\forall t \\forall s (t>=0&0<=s&s<=t->x=5*t->x>=5)".asFormula
  }

  it should "simplify terms 2" in withQE { _ =>
    val fml = "(\\forall t \\forall s (t>=0 & 0 <= s & s<=t -> x=v_0*(0+1*t-0) -> x >= 0))".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=0".asFormula)
    result.subgoals.head.succ should contain only "true".asFormula
  }

  it should "simplify terms 3" in withZ3 { _ =>
    val fml = "x^1>=0^2".asFormula
    val ctxt = IndexedSeq()
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "x>=0".asFormula
  }

  it should "simplify terms when applied to term position" in withQE { _ =>
    val fml = "x=v_0*(0+1*t-0) -> x >= 0".asFormula
    val ctxt = IndexedSeq("x_0=0".asFormula,"v_0=0".asFormula)
    val tactic = simpTac
    val result = proveBy(Sequent(ctxt,IndexedSeq(fml)), tactic(1,PosInExpr(0::1::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x_0=0".asFormula,"v_0=0".asFormula)
    result.subgoals.head.succ should contain only "x=v_0*t -> x>=0".asFormula
  }

  it should "not fail when useFor unification fails" in withQE { _ =>
    val fml = "-X()+Y()>5".asFormula
    val tactic = simpTac
    val result = proveBy(fml, tactic(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "-X()+Y()>5".asFormula
  }

  it should "simplify program auxiliaries in loop" in withQE { _ =>
    //ETCS essentials:
    val fml = ("[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB")))
    pr shouldBe 'proved
    res shouldBe "[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=-b;++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=A;}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "simplify program auxiliaries with precondition" in withQE { _ =>
    //ETCS essentials:
    val fml = ("v^2<=2*b*(m-z)&b>0&A>=0->[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB")))
    pr shouldBe 'proved
    res shouldBe "v^2<=2*b*(m-z)&b>0&A>=0->[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=-b;++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=A;}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "simplify program auxiliaries with multiple preconditions" in withQE { _ =>
    val fml = ("a<=b & b<=c -> v^2<=2*b*(m-z)&b>0&A>=0->[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB")))
    pr shouldBe 'proved
    res shouldBe "a<=b&b<=c->v^2<=2*b*(m-z)&b>0&A>=0->[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=-b;++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);a:=A;}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "leave open bad rewrites" in withQE { _ =>
    val fml = ("v^2<=2*b*(m-z)&b>0&A>=0->[{SB:=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);{?m-z<=SB;a:=-b;++?m-z>=SB;a:=A;}" +
      "t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m").asFormula
    val(res,pr) = rewriteLoopAux(fml,List(Variable("SB"),Variable("a")))
    pr.isProved shouldBe false
    res shouldBe "v^2<=2*b*(m-z)&b>0&A>=0->[{{?m-z<=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);++?m-z>=v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v);}t:=0;{z'=v,v'=a,t'=1&v>=0&t<=ep}}*]z<=m".asFormula
  }

  it should "simplify sole function arguments" in withQE { _ =>
    val fml = "abs(0*1+0)>=0".asFormula
    val result = proveBy(fml, simpTac(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "abs(0)>=0".asFormula
  }

  it should "simplify multiple function arguments" in withQE { _ =>
    val fml = "max(0*1+0, 0+1*y-0)>=0".asFormula
    val result = proveBy(fml, simpTac(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "max(0,y)>=0".asFormula
  }

  it should "not choke on noarg functions" in withQE { _ =>
    val fml = "f()>=0".asFormula
    val result = proveBy(fml, simpTac(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "f()>=0".asFormula
  }

  it should "simplify in quantified" in withQE { _ =>
    val ante = IndexedSeq("x>0".asFormula)
    val succ = IndexedSeq("\\forall y (x>0&y>2)".asFormula)
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(1))
    result.subgoals.head.succ should contain only "\\forall y y>2".asFormula
  }

  it should "simplify in quantified 2" in withQE { _ =>
    val ante = IndexedSeq("x>0".asFormula, "y>3".asFormula)
    val succ = IndexedSeq("\\forall y (x>0&y>2)".asFormula)
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(1))
    result.subgoals.head.succ should contain only "\\forall y y>2".asFormula
  }

  it should "simplify in antecedent" in withQE { _ =>
    val ante = IndexedSeq("true -> x>0*y".asFormula)
    val succ = IndexedSeq()
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(-1))
    result.subgoals.head.ante should contain only "x>0".asFormula
  }

  it should "simplify in antecedent with context" in withQE { _ =>
    val ante = IndexedSeq("x>0".asFormula, "x>0 -> y>3".asFormula)
    val succ = IndexedSeq()
    val result = proveBy(Sequent(ante, succ), SimplifierV2.simpTac(-2))
    result.subgoals.head.ante should contain only ("x>0".asFormula, "y>3".asFormula)
  }

  it should "simplify entire sequent (forwards)" in withQE { _ =>
    val ante = IndexedSeq("x>0".asFormula, "x>0 -> y>3".asFormula, "x>=0 -> y>4".asFormula, "x>0 -> y>5".asFormula,"5=z".asFormula)
    val succ = IndexedSeq("z>3".asFormula)
    val result = proveBy(Sequent(ante, succ), SimplifierV2.fullSimpTac)

    result.subgoals.head.succ should contain only "5>3".asFormula
  }

  it should "simplify entire sequent (forwards) 2" in withQE { _ =>
    val ante = IndexedSeq("x>0 & (x>0 -> y>3) & (x>=0 -> y>4) & (x>0 -> y>5) & 5=z".asFormula)
    val succ = IndexedSeq("z>3".asFormula)
    val result = proveBy(Sequent(ante, succ), SimplifierV2.fullSimpTac)

    println(result)
    result.subgoals.head.succ should contain only "5>3".asFormula
  }


  it should "(attempt to) simplify ground terms" in withQE { _ =>
    val succ = "(1+2+3+4+5+6)^2/6-5-4-3-2*5 = 7".asFormula
    val result = proveBy(succ, SimplifierV2.simpTac(1))
    println(result)
  }

  it should "rewrite simple equalities" in withQE { _ =>
    val fml = "x+y = 0 -> z =0 -> x+y+(x+y)+(x+y+z) = 0".asFormula
    val result = proveBy(fml, SimplifierV2.simpTac(1))
    result.subgoals.head.succ should contain only True
  }

  it should "simplify in manually restricted context" in withQE { _ =>
    val ante = IndexedSeq("a=0".asFormula, "b=0".asFormula, "c=0".asFormula, "d=0".asFormula, "e=0".asFormula)
    val succ = IndexedSeq("a+b+c+d+e = 0".asFormula,"a+b+c+d+e = 0".asFormula)

    val result1 = proveBy(Sequent(ante, succ), SimplifierV2.rsimpTac(IndexedSeq(0,2))(1))
    //Out of bounds positions are thrown out
    val result2 = proveBy(Sequent(ante, succ), SimplifierV2.rsimpTac(IndexedSeq(0,2,5,100,200))(1))
    //Repeated positions are thrown out
    val result3 = proveBy(Sequent(ante, succ), SimplifierV2.rsimpTac(IndexedSeq(1,3,3,3,3))(2))

    result1.subgoals.head.succ should contain only ("b+d+e=0".asFormula,"a+b+c+d+e=0".asFormula)
    result2.subgoals.head.succ should contain only ("b+d+e=0".asFormula,"a+b+c+d+e=0".asFormula)
    result3.subgoals.head.succ should contain only ("a+b+c+d+e=0".asFormula,"a+c+e=0".asFormula)
  }

  it should "work with cases tactic" in withQE { _ =>
    val fml = "(x>=0-> x+y >= 5) & (x < 0 -> x + z <= 5)".asFormula
    val result = proveBy(fml,Idioms.cases((Case("x>0".asFormula),Idioms.ident),(Case("0>=x".asFormula),Idioms.ident)))
    result.subgoals should have size 2
    result.subgoals.head.ante should contain only "x>0".asFormula
    result.subgoals.head.succ should contain only "x+y>=5".asFormula
    result.subgoals.last.ante should contain only "0>=x".asFormula
    result.subgoals.last.succ should contain only "(x>=0 -> x+y>=5) & (x<0 -> x+z<=5)".asFormula
  }

  it should "search for close heuristics" in withQE { _ =>

    val fml = " 0 > x -> x <= 0 & y = 0 & z<x -> x != y+z | x >= 5 -> 5 < x | (x !=5 -> 5<x ) & a = 0 & y = z+a+b & a+z+b = y".asFormula
    val result = proveBy(fml, SimplifierV2.simpTac(1))
    result.subgoals.head.succ should contain only "0>x->y=0&z < x->5 < x|x=5&a=0&0=z+b".asFormula
  }

  it should "pre-expand and use full context before top-level positional simplify" in withQE { _ =>

    val ante = IndexedSeq("P() & Q() & R()".asFormula, "Q() & R()".asFormula)
    val succ = IndexedSeq("P()".asFormula,"Z()".asFormula)

    val result = proveBy(Sequent(ante,succ), SimplifierV2.safeFullSimpTac(1))
    println(result)
  }

}
