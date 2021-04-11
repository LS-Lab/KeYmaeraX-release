/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.btactics


import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.{ToolEvidence, ToolOperationManagement}
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, SlowTest, TodoTest}

import scala.collection.immutable._
import scala.language.postfixOps
import org.scalatest.LoneElement._
import org.scalatest.time.SpanSugar._
import org.scalatest.OptionValues._

import scala.reflect.io.File

/**
 * Tactix Library Test.
 * @author Andre Platzer
 */
@SummaryTest
@UsualTest
class TactixLibraryTests extends TacticTestBase {
  private val someList: () => Iterator[Formula] = () =>
      ("x>=4".asFormula :: "x>=6".asFormula :: "x<2".asFormula :: "x>=5".asFormula :: "x>=0".asFormula :: Nil).iterator

  "DoLoneSome not ChooseSome" should "follow the right cut for x>=7 -> x>=5" in withMathematica { _ =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        cutR("x>=6".asFormula)(SuccPosition(1).top) & OnAll(QE)
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 by invariant" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        diffInvariant("x>=5".asFormula)(1) & dW(1) & QE
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 by loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        loop("x>=5".asFormula)(1) <(
          QE
          ,
          QE
          ,
            solve(1) & OnAll(QE)
      )
    ) shouldBe 'proved
  }

  "ChooseSome" should "find the right cut for x>=7 -> x>=5" in withMathematica { _ =>
    proveBy("x>=7 -> x>=5".asFormula,
      implyR(1) &
        ChooseSome(someList, (c:Formula) => cutR(c)(SuccPosition(1).top) & OnAll(QE & done))
    )
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from one invariant" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        ChooseSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => diffInvariant(inv)(1) & dW(1) & QE & done)
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
      ChooseSome(someList, (inv:Formula) => diffInvariant(inv)(1) & dW(1) & QE & done)
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{x'=x^2}]x>=5 from list of invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{x'=x^2}]x>=5".asFormula,
      implyR(1) &
        //@note master() together with ChooseSome leaves goals open, if first alternative doesn't QE --> demand QE after master
        ChooseSome(someList, (inv:Formula) => diffInvariant(inv)(1) & dW(1) & (master() & QE & done))
    ) shouldBe 'proved
  }


  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from one loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        ChooseSome(() => ("x>=5".asFormula :: Nil).iterator, (inv:Formula) => loop(inv)(1) <(
          QE & done
          ,
          QE & done
          ,
          solve(1) & OnAll(QE & done)
          ))
    ) shouldBe 'proved
  }

  it should "prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        ChooseSome(someList, (inv:Formula) => loop(inv)(1) <(
            QE & done
            ,
            QE & done
            ,
            solve(1) & OnAll(QE & done)
            ))
    ) shouldBe 'proved
  }

  it should "generate and master prove x>=5 -> [{{x'=2}}*]x>=5 from list of loop invariants" in withMathematica { _ =>
    proveBy("x>=5 -> [{{x'=2}}*]x>=5".asFormula,
      implyR(1) &
        //@note master() together with ChooseSome leaves goals open, if first alternative doesn't QE --> demand QE after master
        ChooseSome(someList, (inv:Formula) => loop(inv)(1) & (master() & QE & done))
    ) shouldBe 'proved
  }

  "LetInspect" should "post-hoc instantiate a j closing \\exists j 5+3=j" in withMathematica{ _ =>
    val proof = proveBy("\\exists jj 5+3=jj".asFormula,
      LetInspect("j()".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l, _) => l
        }
        ,
        existsR("j()".asTerm)(1) & SaturateTactic(step(1, 0::Nil))
      ) & byUS(Ax.equalReflexive)
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj 5+3=jj".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc instantiate a j(||) closing \\exists j 5+3=j" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica { _ =>
    val proof = proveBy("\\exists jj 5+3=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l, _) => l
        }
        ,
        existsR("j(||)".asTerm)(1) & SaturateTactic(step(1, 0::Nil))
      ) & byUS(Ax.equalReflexive)
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj 5+3=jj".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc instantiate a j closing \\exists j (x+x)'=j" ignore withMathematica { _ =>
    val proof = proveBy("\\exists jj (x+x)'=jj".asFormula,
      LetInspect("j(.)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l, _) => l
        }
        ,
        existsR("j(x)".asTerm)(1) &
        derive(1, 0::Nil))
        & byUS(Ax.equalReflexive))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x)'=jj".asFormula))
    proof shouldBe 'proved
  }

  /** @see UnificationMatchTest should "unify j()=x+y with s()=s()" unifiable but not by mere matching, needs a proper unifier instead of a single sided matcher */
  it should "post-hoc find a j() closing (x+x*y)'=j()" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica { _ =>
    val proof = proveBy("\\exists jj (x+x*y)'=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l, _) => l
        }
        ,
        existsR("j()".asTerm)(1) &
          derive(1, 0::Nil))
        & byUS(Ax.equalReflexive))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x*y)'=jj".asFormula))
    proof shouldBe 'proved
  }

  /** @see UnificationMatchTest should "unify j()=x+y with s()=s()" */
  it should "post-hoc find a j() closing j()=(x+x*y)'" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica { _ =>
    val proof = proveBy("\\exists jj jj=(x+x*y)'".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(_, r) => r
        }
        ,
        existsR("j()".asTerm)(1) &
        derive(1, 1::Nil))
        & byUS(Ax.equalReflexive))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj jj=(x+x*y)'".asFormula))
    proof shouldBe 'proved
  }

  it should "post-hoc find a j(||) closing (x+x*y)'=j(||)" taggedAs(TodoTest,IgnoreInBuildTest) ignore withMathematica{ _ =>
    val proof = proveBy("\\exists jj (x+x*y)'=jj".asFormula,
      LetInspect("j(||)".asTerm,
        (pr:ProvableSig) => pr.subgoals.head.succ.head match {
          case Equal(l, _) => l
        }
        ,
        existsR("j(||)".asTerm)(1) &
          derive(1, 0::Nil))
        & byUS(Ax.equalReflexive))
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("\\exists jj (x+x*y)'=jj".asFormula))
    proof shouldBe 'proved
  }

  def feedOneAfterTheOther[A<:Expression](list: List[A]) : (ProvableSig,ProverException)=>Seq[Expression] = {
    var rem = list
    (_,e) => println("SnR loop status " + e)
      rem match {
        case hd::tail => rem = tail; hd :: Nil
        case _ => throw new BelleNoProgress("SearchAndRescueAgain ran out of alternatives among: " + list)
      }
  }

  "sAI" should "prove x>=0 -> [{x'=x^2+x+1}]x>=0" in withMathematica { _ =>
    val fml = "x>=0 -> [{x'=x^2+x+1}]x>=0".asFormula
    proveBy(fml, implyR(1) & ODEInvariance.sAIclosedPlus()(1)) shouldBe 'proved
  }

  "loopPostMaster" should "find an invariant for x=5-> [{x:=x+2;{x'=1}}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;{x'=1}}*]x>=0".asFormula
    val invs = List("x>=-1".asFormula, "x=5".asFormula, "x>=0".asFormula, "x=7".asFormula).map(_ -> None).toStream
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs)(1)) shouldBe 'proved
    //@note postcondition is invariant, loopPostMaster won't ask invariant generator
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for curvebot" in withMathematica { _ =>
    val fml = """x!=ox | y!=oy ->
                #  [{
                #    {?(x+w/-1-ox)^2+(y-v/-1-oy)^2!=v^2+w^2; om:=-1;
                #    ++ ?(x+w-ox)^2+(y-v-oy)^2!=v^2+w^2; om:=1;
                #    ++ ?(ox-x)*w!=(oy-y)*v; om:=0;}
                #    {x'=v,y'=w,v'=om*w,w'=-om*v}
                #   }*
                #  ] !(x=ox & y=oy)""".stripMargin('#').asFormula
    //@note postcondition is invariant
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "find an invariant for curvebot with fns" in withMathematica { _ =>
    val fml = """x!=ox() | y!=oy() ->
                #  [{
                #    {?(x+w/-1-ox())^2+(y-v/-1-oy())^2!=v^2+w^2; om:=-1;
                #    ++ ?(x+w-ox())^2+(y-v-oy())^2!=v^2+w^2; om:=1;
                #    ++ ?(ox()-x)*w!=(oy()-y)*v; om:=0;}
                #    {x'=v,y'=w,v'=om*w,w'=-om*v}
                #   }*
                #  ] !(x=ox() & y=oy())""".stripMargin('#').asFormula
    //@note postcondition is invariant
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => Nil.toStream)(1)) shouldBe 'proved
  }

  it should "eventually run out of ideas" taggedAs SlowTest in withQE { _ =>
    val s = "x>=0, x=H(), v=0, g()>0, 1>=c(), c()>=0 ==> [{{x'=v,v'=-g()&x>=0}{?x=0;v:=-c()*v;++?x!=0;}}*](x>=0&x<=H())".asSequent
    // defaultInvariantGenerator does not find an invariant, so loopPostMaster should eventually run out of ideas and
    // not keep asking over and over again
    failAfter(50 seconds) {
      val result = the[BelleThrowable] thrownBy proveBy(s, loopPostMaster(invGenerator)(1))
      result.getMessage should include("loopPostMaster: Invariant generator ran out of ideas")
    }
  }

  //@todo why do these tests fail with ill-positioning?
  "SnR Loop Invariant" should "by loopSR find an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val proof = proveBy(fml,
      implyR(1) & loopSR((_, _) => invs.map(_ -> None).toStream)(1)
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
    proveBy(fml, implyR(1) & loopSR((_, _) => invs.map(_ -> None).toStream)(1)) shouldBe 'proved
  }

  it should "by loopPostMaster find an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val proof = proveBy(fml,
      implyR(1) & loopPostMaster((_, _) => invs.map(_ -> None).toStream)(1)
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
    proveBy(fml, implyR(1) & loopPostMaster((_, _) => invs.map(_ -> None).toStream)(1)) shouldBe 'proved
  }

  it should "find by assignb an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val jj = "j(.)".asFormula
    val proof = proveBy(fml,
      implyR(1) & SearchAndRescueAgain(jj :: Nil,
        loop(USubst(Seq(SubstitutionPair(".".asTerm,"x".asTerm)))(jj))(1) <(nil, nil, assignb(1)),
        feedOneAfterTheOther(invs),
        OnAll(master()) & done
      )
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
    proveBy(fml, implyR(1) & loopSR((_, _) => invs.map(_ -> None).toStream)(1)) shouldBe 'proved
  }

  it should "find by step an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val jj = "j(.)".asFormula
    val proof = proveBy(fml,
      implyR(1) & SearchAndRescueAgain(jj :: Nil,
        loop(USubst(Seq(SubstitutionPair(".".asTerm,"x".asTerm)))(jj))(1) <(nil, nil, step(1)),
        feedOneAfterTheOther(invs),
        OnAll(master()) & done
      )
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
    proveBy(fml, implyR(1) & loopSR((_, _) => invs.map(_ -> None).toStream)(1)) shouldBe 'proved
  }

  it should "find by chase an invariant for x=5-> [{x:=x+2;}*]x>=0" in withMathematica { _ =>
    val fml = "x>=5 -> [{x:=x+2;}*]x>=0".asFormula
    val invs = List(".>=-1".asFormula, ".=5".asFormula, ".>=0".asFormula)
    val jj = "j(.)".asFormula
    val proof = proveBy(fml,
      implyR(1) & SearchAndRescueAgain(jj :: Nil,
        loop(USubst(Seq(SubstitutionPair(".".asTerm,"x".asTerm)))(jj))(1) <(nil, nil, chase(1)),
        feedOneAfterTheOther(invs),
        OnAll(master()) & done
      )
    )
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq(fml))
    proof shouldBe 'proved
    proveBy(fml, implyR(1) & loopSR((_, _) => invs.map(_ -> None).toStream)(1)) shouldBe 'proved
  }

  "Normalize" should "prove simple formula" in {
    val f = "y>0 -> [x:=y;]x>0".asFormula
    proveBy(f, normalize) shouldBe 'proved
  }

  it should "unfold simple formula" in {
    val f = "y>0 -> [x:=2;]x>0".asFormula
    proveBy(f, normalize).subgoals.loneElement shouldBe "y>0 ==> 2>0".asSequent
  }

  it should "unfold simple formula when other formulas are around" in {
    val f = "y>0 -> y>=0 | [x:=2;]x>0".asFormula
    proveBy(f, normalize).subgoals.loneElement shouldBe "y>0 ==> y>=0, 2>0".asSequent
  }

  it should "unfold with ODE when other formulas are around" in {
    val f = "y>0 -> y>=0 | [x:=2;{x'=3}]x>0".asFormula
    proveBy(f, normalize).subgoals.loneElement shouldBe "y>0, x=2 ==> y>=0, [{x'=3}]x>0".asSequent
  }

  it should "not unfold FOL formulas" in {
    val f = "y>0 -> y>=0 & y>=-1".asFormula
    proveBy(f, normalize).subgoals.loneElement shouldBe "y>0 ==> y>=0 & y>=-1".asSequent
  }

  it should "not unfold FOL negations" in {
    val f = "y>0 -> !y>=0 | y>=-1".asFormula
    proveBy(f, normalize).subgoals.loneElement shouldBe "y>0 ==> !y>=0, y>=-1".asSequent
  }

  it should "unfold non-FOL formulas" in {
    val f = "y>0 -> ![y:=-1;]y>=0 & y>=-1".asFormula
    val result = proveBy(f, normalize)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe "y>0, -1>=0 ==> ".asSequent
    result.subgoals(1) shouldBe "y>0 ==> y>=-1".asSequent
  }

  it should "unfold non-predicatefree-FOL formulas" in withQE { _ =>
    val f = "(y>0->p(x)) -> p(y)".asFormula
    val result = proveBy(f, normalize)
    result.subgoals should have size 2
    result.subgoals(0) shouldBe " ==> p(y), y>0".asSequent
    result.subgoals(1) shouldBe "p(x) ==> p(y)".asSequent
  }

  it should "auto modus ponens" in withQE { _ =>
    val f = "(y>0->p(x)) -> (y>0 -> p(y))".asFormula
    //@todo chase first traverse into autoMP in antecedent before working on implyR, so autoMP creates an additional
    // y>0 since it is not available verbatim yet
    proveBy(f, normalize).subgoals.loneElement shouldBe "p(x), y>0, y>0 ==> p(y)".asSequent
  }

  it should "not fail when trying to chase non-toplevel" in {
    val f = "X>x&\\forall a (x<a&a<=X->a<=Y) -> \\exists a (a>x&a<=Y)".asFormula
    //@note master does not yet instantiate quantifiers, but tries to chase inside
    proveBy(f, normalize).subgoals.loneElement shouldBe "X>x, \\forall a (x<a&a<=X->a<=Y) ==> \\exists a (a>x&a<=Y)".asSequent
  }

  it should "chase non-toplevel" in {
    val f = "X>x&\\forall a ([x:=2;]x<a&a<=X->[z:=Y;]a<=z) -> \\exists a (a>x&a<=Y)".asFormula
    //@note master does not yet instantiate quantifiers, but tries to chase inside
    proveBy(f, normalize).subgoals.loneElement shouldBe "X>x, \\forall a (2<a&a<=X->a<=Y) ==> \\exists a (a>x&a<=Y)".asSequent
  }

  it should "unfold in succedent and antecedent" in {
    val result = proveBy(
      """v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw(), A()>0, B()>=b(), b()>0, ep()>0, lw()>0
        #==>
        #(abs(y-ly())+v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < lw()
        #->  \forall a (-B()<=a&a<=A()->\forall w \forall r (r!=0&w*r=v->\forall c (c=0->[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())))))
        #  & (v=0->\forall w (w=0->\forall c (c=0->[{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw()))))
        #  & \forall a (-B()<=a&a<=-b()->\forall c (c=0->[{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())))""".stripMargin('#').asSequent, normalize)
    result.subgoals should have size 3
    result.subgoals(0) shouldBe "A()>0, B()>=b(), b()>0, ep()>0, lw()>0, abs(y-ly())+v^2/(2*b())+(A()/b()+1)*(A()/2*ep()^2+ep()*v) < lw(), -B()<=a, a<=A(), r!=0, w*r=v, c=0, v>=0, dx^2+dy^2=1, r_0!=0, abs(y-ly())+v^2/(2*b()) < lw() ==> [{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())".asSequent
    result.subgoals(1) shouldBe "A()>0, B()>=b(), b()>0, ep()>0, lw()>0, v=0, w=0, c=0, v>=0, dx^2+dy^2=1, r!=0, abs(y-ly())+v^2/(2*b()) < lw() ==> [{x'=v*dx,y'=v*dy,v'=0,dx'=-dy*w,dy'=dx*w,w'=0/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())".asSequent
    result.subgoals(2) shouldBe "A()>0, B()>=b(), b()>0, ep()>0, lw()>0, -B()<=a, a<=-b(), c=0, v>=0, dx^2+dy^2=1, r!=0, abs(y-ly())+v^2/(2*b()) < lw() ==> [{x'=v*dx,y'=v*dy,v'=a,dx'=-dy*w,dy'=dx*w,w'=a/r,c'=1&v>=0&c<=ep()}](v>=0&dx^2+dy^2=1&r!=0&abs(y-ly())+v^2/(2*b()) < lw())".asSequent
  }

  it should "use abstraction" in {
    val f = "x>=0 -> [y:=y+1;]x>=0".asFormula
    proveBy(f, normalize) shouldBe 'proved
  }

  it should "inherit labels from core rules" in {
    proveBy("x>=0 | y>=0 -> [z:=x; ++ z:=y;{z'=1}](z=x | z>=y)".asFormula, normalize, _.value should contain theSameElementsAs
      "[z:=x;](z=x|z>=y)::[z:=y;{z'=1}](z=x|z>=y)".asLabels
    ).subgoals should contain theSameElementsAs List(
      "x>=0|y>=0 ==> x=x, x>=y".asSequent,
      "x>=0|y>=0, z=y ==> [{z'=1}](z=x|z>=y)".asSequent
    )
  }

  it should "apply tactics on core labels" in withQE { _ =>
    val bt = List("[z:=x;](z=x|z>=y)".asLabel -> useAt(Ax.equalRefl)(1), "[z:=y;{z'=1}](z=x|z>=y)".asLabel -> solve(1)).permutations
    bt.foreach(t =>
      proveBy("x>=0 | y>=0 -> [z:=x; ++ z:=y;{z'=1}](z=x|z>=y)".asFormula, normalize & CaseTactic(t)).subgoals should contain theSameElementsAs List(
        "x>=0|y>=0 ==> true, x>=y".asSequent,
        "x>=0|y>=0, z=y ==> \\forall t_ (t_>=0 -> t_+z=x|t_+z>=y)".asSequent
      ))
  }

  "QE" should "reset timeout when done" in withQE {
    case tool: ToolOperationManagement =>
      val origTimeout = tool.getOperationTimeout
      origTimeout shouldBe Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))
      proveBy("x>1 -> x>0".asFormula, QE(Nil, None, Some(7)) & anon ((provable: ProvableSig) => {
          tool.getOperationTimeout shouldBe origTimeout // timeout should be reset after QE
          provable
        })
      ) shouldBe 'proved
    case _ => // nothing to test
  }

  it should "reset timeout when failing" in withQE {
    case tool: ToolOperationManagement =>
      val origTimeout = tool.getOperationTimeout
      origTimeout shouldBe Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))
      proveBy("x>0 -> x>1".asFormula, QE(Nil, None, Some(7)) | anon ((provable: ProvableSig) => {
          tool.getOperationTimeout shouldBe origTimeout // timeout should be reset after QE
          provable
        })
      ) should (not be 'proved)
    case _ => // nothing to test
  }

  it should "not change timeout before being run" in withQE {
    case tool: ToolOperationManagement =>
      val origTimeout = tool.getOperationTimeout
      origTimeout shouldBe Integer.parseInt(Configuration(Configuration.Keys.QE_TIMEOUT_MAX))
      proveBy("x>0 -> x>1".asFormula, (DebuggingTactics.assert(_ => false, "Skip QE", new TacticInapplicableFailure(_))
          & QE(Nil, None, Some(7))) | anon ((provable: ProvableSig) => {
          tool.getOperationTimeout shouldBe origTimeout // timeout should be reset after QE
          provable
        })
      ) should (not be 'proved)
    case _ => // nothing to test
  }

  "Tactic chase" should "not infinite recurse" in withQE { _ =>
    var i = 0
    val count = anon ((_: Position, _: Sequent) => { i=i+1; skip })

    failAfter(2 seconds) {
      val result = proveBy("[{x'=1}]x>0".asFormula, master(loopauto(), count, keepQEFalse=false))
      // master uses solve after count does not make progress
      result.subgoals.loneElement shouldBe "t_>=0 ==> t_+x>0".asSequent
    }

    i shouldBe 2 /* decomposeToODE calls ODE, and so is master after decomposeToODE is done */
  }

  it should "not apply stutter axioms infinitely" in withQE { _ =>
    proveBy("[x:=x+1;][{x'=1}]j(x)".asFormula, chase(1))
  }

  it should "exhaustively apply propositional" in withTactics {
    proveBy("true<->(p()<->q())&q()->p()".asFormula, prop) shouldBe 'proved
  }

  it should "inherit labels from core rules with prop" in {
    proveBy("x>=0 | y>=0 -> x^2>=0 & y^2>=0".asFormula, prop, _.value should contain theSameElementsAs
      "x>=0//x^2>=0::y>=0//x^2>=0::x>=0//y^2>=0::y>=0//y^2>=0".asLabels
    )
  }

  it should "chase at position" in withTactics {
    val result = proveBy("==> x>1 -> x>0, y>2 -> [y:=y+2;y:=y+1;]y>5".asSequent, tacticChase()(implyR,step)(None)(2))
    result.subgoals.loneElement shouldBe "y>2 ==> x>1 -> x>0, y+2+1>5".asSequent
  }

  it should "search for expected formula if positions shifted" in withTactics {
    val result = proveBy("==> x>1 -> x>0, y>2 -> [y:=y+2;y:=y+1;]y>5".asSequent,
      implyR(1) & tacticChase()(implyR,step)(Some("y>2 -> [y:=y+2;y:=y+1;]y>5".asFormula))(2))
    result.subgoals.loneElement shouldBe "x>1, y>2 ==> x>0, y+2+1>5".asSequent
  }

  it should "chase everywhere" in withTactics {
    val result = proveBy("==> x>1 -> x>0, y>2 -> [y:=y+2;y:=y+1;]y>5".asSequent, allTacticChase()(implyR,step))
    result.subgoals.loneElement shouldBe "x>1, y>2 ==> x>0, y+2+1>5".asSequent
  }

  it should "chase multiple tactic options" in withMathematica { _ =>
    val result = proveBy("l() < r(), l()<=x, x<=r(), x=l() ==> [{x'=1&l()>=x|x>=r()}](l()<=x&x<=r())".asSequent,
      allTacticChase()(ODE, solve))
    result.subgoals.loneElement shouldBe "l() < r(), l()<=x_0, x_0<=r(), x_0=l(), l()>=x_0|x_0>=r(), time_=0, x_0=x ==> \\forall t_ (t_>=0->\\forall s_ (0<=s_&s_<=t_->(l()>=s_+x|s_+x>=r())&s_+time_>=0&s_+x=s_+time_+x_0)->t_+x<=r())".asSequent
  }

  "Loop convergence" should "prove x>=0 -> <{x:=x-1;}*>x<1 with conRule" in withMathematica { _ =>
    val fml = "x>=0 -> <{x:=x-1;}*>x<1".asFormula
    val vari = "x<v+1".asFormula
    proveBy(fml, implyR(1) & DLBySubst.conRule("v".asVariable, vari)(1)).subgoals shouldBe IndexedSeq(
      Sequent(IndexedSeq("x>=0".asFormula), IndexedSeq("\\exists v x<v+1".asFormula)),
      Sequent(IndexedSeq("v<=0".asFormula, "x<v+1".asFormula), IndexedSeq("x<1".asFormula)),
      Sequent(IndexedSeq("v>0".asFormula, "x<v+1".asFormula), IndexedSeq("<x:=x-1;>x<(v-1)+1".asFormula))
    )
    proveBy(fml, implyR(1) & DLBySubst.conRule("v".asVariable, vari)(1) <(
      debug("init") & QE(),
      debug("use") & QE(),
      debug("step") & assignd(1) & QE()
      ))
  }

  it should "prove x>=0 -> <{x:=x-1;}*>x<1 with con" in withMathematica { _ =>
    val fml = "x>=0 -> <{x:=x-1;}*>x<1".asFormula
    val vari = "x<v+1".asFormula
    proveBy(fml, implyR(1) & con("v".asVariable, vari)(1)).subgoals shouldBe IndexedSeq(
      "x>=0 ==> \\exists v x<v+1".asSequent,
      "v<=0, x<v+1 ==> x<1".asSequent,
      "v>0, x<v+1 ==> <x:=x-1;>x<(v-1)+1".asSequent
    )
    proveBy(fml, implyR(1) & DLBySubst.conRule("v".asVariable, vari)(1) <(
      debug("init") & QE(),
      debug("use") & QE(),
      debug("step") & assignd(1) & QE()
      ))
  }

  it should "prove x>=0 & c=1 -> <{x:=x-c;}*>x<1 with con" in withMathematica { _ =>
    val fml = "x>=0 & c=1 -> <{x:=x-c;}*>x<1".asFormula
    val vari = "x<z+1".asFormula
    proveBy(fml, implyR(1) & andL(-1) & con("z".asVariable, vari)(1)).subgoals shouldBe IndexedSeq(
      "x>=0, c=1 ==> \\exists z x<z+1".asSequent,
      "z<=0, x<z+1, c=1 ==> x<1".asSequent,
      "z>0, x<z+1, c=1 ==> <x:=x-c;>x<(z-1)+1".asSequent
    )
    proveBy(fml, implyR(1) & con("z".asVariable, vari)(1) <(
      debug("init") & QE(),
      debug("use") & QE(),
      debug("step") & assignd(1) & QE()
      ))
  }

  "Master" should "not split unnecessarily early" in withMathematica ({ _ =>
    val fml = """
                |  /* INITIAL CONDITIONS */
                |  (velCtrl >= 0 & velLead >= 0 & A > 0 & B > 0 & T > 0 & posCtrl <= posLead &
                |  /* The car has to be safe in the 'worst case' where the lead car brakes to a
                |     stop. This means that we must be able to brake to a stop as before we
                |     reach the lead car's final position */
                |  posCtrl + velCtrl^2/(2*B) <= posLead + velLead^2 /(2*B))
                |  ->
                |  [
                |    {
                |      /* CONTROL */
                |      {
                |        /* We only allow accelerations where after accelerating for time
                |           T, we are still safe (by the above definition).
                |           Note that the lead car might already start braking to a stop in this
                |           scenario.
                |           Therefore, our final position after 1 acceleration cycle then
                |           braking to a stop must be <= the lead car's final position if it
                |           brakes to a stop right now.
                |           {a:=A; ? a>=0 & a <= A &
                |            (posCtrl + velCtrl * T + a/2 * T^2) + (velCtrl+a*T)^2/(2*B) <=
                |            (posLead + velLead^2/(2*B)); accCtrl:=a;}
                |        */
                |        {
                |          {?((posCtrl + velCtrl * T + A/2 * T^2) + (velCtrl+A*T)^2/(2*B) <=
                |            (posLead + velLead^2/(2*B))); accCtrl:=A;}
                |          ++
                |          {if (velCtrl = 0) {accCtrl:=0;} else {accCtrl := -B;}}
                |        }
                |        {
                |          accLead := A;
                |          ++
                |          {if (velLead = 0) {accLead:=0;} else {accLead := -B;}}
                |        }
                |      }
                |      /* CONTINUOUS DYNAMICS */
                |      t := 0;
                |      {
                |        { posLead' = velLead, velLead' = accLead,
                |          posCtrl' = velCtrl, velCtrl' = accCtrl , t' = 1 &
                |          (velCtrl >= 0 & velLead >= 0 & t <= T)
                |        } /* evolution domain and event-trigger */
                |      }
                |    }*@invariant(
                |      posCtrl <= posLead &
                |      posCtrl + velCtrl^2/(2*B) <= posLead + velLead^2 /(2*B) &
                |      velLead >= 0 & velCtrl >= 0)
                |  ]
                |  (posCtrl <= posLead) /* safety condition */""".stripMargin.asFormula

    proveBy(fml, master()) shouldBe 'proved
  }, 180)

  it should "apply ODE duration heuristic to multiple ODEs" in withZ3 { _ =>
    val problem = ArchiveParser.parser(
      """Theorem ""
        |Problem
        |x < -4
        |  ->
        |  [
        |     t := 0;
        |     v := 4;
        |     {x' = v, t' = 1 & t <= 1};
        |     a := 8/x;
        |     {x' = v, v' = a & v >= 0}
        |  ] x <= 0
        |End.
        |End.""".stripMargin).head.model.asInstanceOf[Formula]

    proveBy(problem, master()) shouldBe 'proved
  }

  it should "prove the bouncing ball with invariant annotation" in withQE { _ =>
    val problem = ArchiveParser.getEntry("Bouncing Ball", io.Source.fromInputStream(
      getClass.getResourceAsStream("/keymaerax-projects/lics/bouncing-ball.kya")).mkString).get.model.asInstanceOf[Formula]
    proveBy(problem, master()) shouldBe 'proved
  }

  it should "prove regardless of order" taggedAs SlowTest in withQE { _ =>
    val problem1 = """
      v^2<=2*b*(m-x) & v>=0  & A>=0 & b>0
      -> [
           {
             {?(v+A*ep)^2<=2*b*(m-x-A/2*ep^2-v*ep) ; a :=A; ++ a:=-b;}
             t := 0;
             {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
           }*
         ] x <= m""".stripMargin(' ').asFormula
    proveBy(problem1, master()) shouldBe 'proved

    val problem2 = """
      v^2<=2*b*(m-x) & v>=0  & A>=0 & b>0
      -> [
           {
             {a:=-b; ++ ?(v+A*ep)^2<=2*b*(m-x-A/2*ep^2-v*ep) ; a :=A; }
             t := 0;
             {x'=v, v'=a, t'=1 & v>=0 & t<=ep}
           }*
         ] x <= m""".stripMargin(' ').asFormula
    proveBy(problem2, master()) shouldBe 'proved
  }

  it should "try the postcondition" in withQE { _ =>
    val fml = "x<y -> [{if (x>0) { x:=-x; } else { x:=y; } }*]x<=y".asFormula
    proveBy(fml, master()) shouldBe 'proved
  }

  it should "try the preocondition" in withQE { _ =>
    val fml = "x<y -> [{if (x>0) { x:=-x; } else { x:=x-1/(y-x); } }*]x<=y".asFormula
    proveBy(fml, master()) shouldBe 'proved
  }

  it should "apply safeabstraction and find the correct recursors" in withQE { _ =>
    // provable with safeabstraction, which is an anon tactic; triggers master autoTacticIndex comparison with loop and
    // returns wrong recursor if autoTacticIndex comparison bug
    proveBy("x>=0 -> [y:=2;]x>=0".asFormula, master()) shouldBe 'proved
  }

  it should "use auto modus ponens" in withQE { _ =>
    val s = "Y>y, X>y, y < x&x<=Y->P(x) ==>  y < x&x<=min(X,Y)->P(x)".asSequent
    proveBy(s, master()) shouldBe 'proved
  }

  it should "not fail when trying to chase non-toplevel" in withQE { _ =>
    val f = "\\exists X (X>x&\\forall a (x<a&a<=X->P(a)))->\\exists a (a>x&P(a))".asFormula
    //@note master does not yet instantiate quantifiers
    proveBy(f, master()).subgoals.loneElement shouldBe "X>x, \\forall a (x<a&a<=X->P(a)) ==> \\exists a (a>x&P(a))".asSequent
  }

  "useLemma" should "use unification to bridge between function symbols and terms" in withTactics {
    val lemmaName = "tests/useLemma/tautology1"
    val lemma = proveBy("f()>0 -> f()>0".asFormula, prop)
    lemma shouldBe 'proved
    LemmaDBFactory.lemmaDB.add(Lemma(lemma, Lemma.requiredEvidence(lemma), Some("user" + File.separator + lemmaName)))
    proveBy("==> f()>0 -> f()>0".asSequent, useLemmaX(lemmaName, None)) shouldBe 'proved
    proveBy("==> x>0 -> x>0".asSequent, useLemmaX(lemmaName, None)) shouldBe 'proved
    proveBy("==> x^2+y>0 -> x^2+y>0".asSequent, useLemmaX(lemmaName, None)) shouldBe 'proved
  }

  it should "use recorded substitutions" in withTactics {
    val lemmaName = "tests/useLemma/tautology2"
    val subst = USubst("f(x) ~> x^2".asSubstitutionPair :: Nil)
    val lemma = proveBy("f(x)>0 -> f(x)>0".asFormula, US(subst) & prop, subst=subst)
    lemma shouldBe 'proved
    LemmaDBFactory.lemmaDB.add(Lemma(lemma,
      Lemma.requiredEvidence(lemma, ToolEvidence(List("tactic" -> """US("f(x)~>x^2"); prop"""))::Nil),
      Some("user" + File.separator + lemmaName)))
    proveBy("==> x^2>0 -> x^2>0".asSequent, useLemmaX(lemmaName, None)) shouldBe 'proved
    val result = proveBy("==> f(x)>0 -> f(x)>0".asSequent, useLemmaX(lemmaName, None))
    result shouldBe 'proved
    result.conclusion shouldBe "==> x^2>0 -> x^2>0".asSequent
  }

  it should "use definitions" in withTactics {
    val lemmaName = "tests/useLemma/tautology2"
    val entry = ArchiveParser(
      """Lemma "Lemma 1"
        |Definitions Real f(Real x)=x^2; End.
        |ProgramVariables Real x; End.
        |Problem f(x)>0->f(x)>0 End.
        |End.""".stripMargin).head
    val subst = USubst(entry.defs.substs)
    val SubstitutionPair(FuncOf(f, _), _) = subst.subsDefsInput.head
    val lemma = proveBy("f(x)>0 -> f(x)>0".asFormula, Expand(f, entry.defs.substs.head) & prop, subst=subst)
    lemma shouldBe 'proved
    LemmaDBFactory.lemmaDB.add(Lemma(lemma,
      Lemma.requiredEvidence(lemma, ToolEvidence(List("model" -> entry.fileContent, "tactic" -> """expand "f"; prop"""))::Nil),
      Some("user" + File.separator + lemmaName)))
    proveBy("==> x^2>0 -> x^2>0".asSequent, useLemmaX(lemmaName, None)) shouldBe 'proved
    val result = proveBy("==> f(x)>0 -> f(x)>0".asSequent, useLemmaX(lemmaName, None))
    result shouldBe 'proved
    result.conclusion shouldBe "==> x^2>0 -> x^2>0".asSequent
  }

  it should "cut in lemma conclusion as assumption when lemma doesn't close" in withTactics {
    val lemmaName = "tests/useLemma/tautology2"
    val subst = USubst("f(x) ~> x^2".asSubstitutionPair :: Nil)
    val lemma = proveBy("f(x)>0 -> f(x)>0".asFormula, US(subst) & prop, subst=subst)
    lemma shouldBe 'proved
    lemma.conclusion shouldBe "==> x^2>0 -> x^2>0".asSequent
    LemmaDBFactory.lemmaDB.add(Lemma(lemma,
      Lemma.requiredEvidence(lemma, Lemma.requiredEvidence(lemma, ToolEvidence(List("tactic" -> """US("f(x)~>x^2"); prop"""))::Nil)),
      Some("user" + File.separator + lemmaName)))
    proveByS("==> 2*x>0 -> 2*x>0".asSequent, useLemmaX(lemmaName, None), _.value should contain theSameElementsAs List(
      "Use//Lemma available as assumption".asLabel
    )).subgoals.loneElement shouldBe
      "x^2>0 -> x^2>0 ==> 2*x>0->2*x>0".asSequent
  }

  "useLemmaAt" should "apply at provided key" in withQE { _ =>
    val lemmaName = "tests/useLemmaAt/tautology1"
    val lemma = proveBy("p() -> p()&p()".asFormula, prop)
    lemma shouldBe 'proved
    LemmaDBFactory.lemmaDB.add(Lemma(lemma, Lemma.requiredEvidence(lemma), Some("user" + File.separator + lemmaName)))
    proveBy("==> x=0 & x=0".asSequent, useLemmaAt(lemmaName, Some(PosInExpr(1::Nil)))(1)).subgoals.loneElement shouldBe "==> x=0".asSequent
    proveBy("x=0 ==> ".asSequent, useLemmaAt(lemmaName, Some(PosInExpr(0::Nil)))(-1)).subgoals.loneElement shouldBe "x=0 & x=0 ==> ".asSequent
  }

  it should "apply with default key .1 in succedent" in withQE { _ =>
    val lemmaName = "tests/useLemmaAt/tautology1"
    val lemma = proveBy("p() -> p()&p()".asFormula, prop)
    lemma shouldBe 'proved
    LemmaDBFactory.lemmaDB.add(Lemma(lemma, Lemma.requiredEvidence(lemma), Some("user" + File.separator + lemmaName)))
    proveBy("==> x=0 & x=0".asSequent, useLemmaAt(lemmaName, None)(1)).subgoals.loneElement shouldBe "==> x=0".asSequent
  }

  it should "apply with default key .0 in antecedent" in withQE { _ =>
    val lemmaName = "tests/useLemmaAt/tautology1"
    val lemma = proveBy("p() -> p()&p()".asFormula, prop)
    lemma shouldBe 'proved
    LemmaDBFactory.lemmaDB.add(Lemma(lemma, Lemma.requiredEvidence(lemma), Some("user" + File.separator + lemmaName)))
    proveBy("x=0 ==> ".asSequent, useLemmaAt(lemmaName, Some(PosInExpr(0::Nil)))(-1)).subgoals.loneElement shouldBe "x=0 & x=0 ==> ".asSequent
  }

}
