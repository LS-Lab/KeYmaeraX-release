/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{Matchers, FlatSpec}
import testHelper.StringConverter._

import scala.collection.immutable

/**
 * Created by nfulton on 5/21/15.
 */
class CoreChangesDebugging extends FlatSpec with Matchers {
  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val t = Variable("t", None, Real)
  val tFun = FuncOf(Function("t", None, Unit, Real), Nothing)
  val p = Function("p", None, Real, Bool)
  val pany = PredOf(p, Anything)
  val pdot = PredOf(p, DotTerm)

  def N(n:Int) = Number(n)

  def succSeq(f : Formula) = new Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq(f))

  "Uniform substitution" should "setup" in {
    // \forall x. p(x) -> p(t()).
    def formula(lhs : Formula, rhs : Formula) = Forall(immutable.Seq(x), Imply(lhs, rhs))
    val originalF = formula(PredOf(p, x), PredOf(p, tFun))
    val expectedF = formula(Equal(x, N(0)), Equal(x, N(0)))

    val original = succSeq(originalF)
    val expected = succSeq(expectedF)

    val substitution =
      new SubstitutionPair(tFun, y) ::
      new SubstitutionPair(PredOf(p, Anything), Equal(x, N(0))) ::
      Nil

    //Will throw an exception if the substitution doesn't work out.
    val result = UniformSubstitutionRule(USubst(substitution), original).apply(expected)
  }

  "Uniform substitution" should "not fail -- simple car" in {
    val pReplacement = Box(Assign(x, DotTerm), PredOf(p, Anything))

    // \forall x. p(x) -> p(t()).
    def formula(subF : Formula) = Forall(immutable.Seq(x), subF)
    val originalF = formula(PredOf(p, x))
    val expectedF = formula(pReplacement)

    val original = succSeq(originalF)
    val expected = succSeq(expectedF)

    val substitution =
      new SubstitutionPair(tFun, y) ::
        new SubstitutionPair(PredOf(p, Anything), pReplacement) ::
        Nil

    //Will throw an exception if the substitution doesn't work out.
    val result = UniformSubstitutionRule(USubst(substitution), original).apply(expected)
  }

  it should "not fail $abstractiondummy ex" in {
    val f = Forall(x :: Nil, Imply(pany, pany))

    val substitution = new SubstitutionPair(tFun, x) ::
      new SubstitutionPair(pany, Forall(x ::Nil, DifferentialFormula(pany))) ::
      Nil

    val expected = Forall(x :: Nil, Imply(Forall(x ::Nil, DifferentialFormula(pany)), Forall(x ::Nil, DifferentialFormula(pany))))

    val result = UniformSubstitutionRule(USubst(substitution), succSeq(f)).apply(succSeq(expected))
  }


  /*
   * Reproducing:
   * Substitution clash: USubst{(t()~>$abstractiondummy), (p(•)~>\forall x.p(?)'<->\forall x.(p(?))')} not {$abstractiondummy}-admissible for p($abstractiondummy) when substituting in \forall $abstractiondummy.p($abstractiondummy)
in Sequent[{(),  ==> \forall $abstractiondummy.p($abstractiondummy)->p(t())}]
in USubst{(t()~>$abstractiondummy), (p(•)~>\forall x.p(?)'<->\forall x.(p(?))')}
on premise   Sequent[{(),  ==> \forall $abstractiondummy.p($abstractiondummy)->p(t())}]
resulted in  clash top except {$abstractiondummy}
but expected Sequent[{(),  ==> \forall $abstractiondummy.(\forall x.p(?)'<->\forall x.(p(?))')->(\forall x.p(?)'<->\forall x.(p(?))')}]
   */
  it should "reproduce forall derive problem" in {
    val ad = Variable("$abstractiondummy", None, Real)
    val substitution =
      new SubstitutionPair(tFun, ad) ::
      new SubstitutionPair(pdot, Equiv(DifferentialFormula(Forall(x::Nil, pany)), Forall(x::Nil, DifferentialFormula(pany)))) ::
      Nil

    val f = Forall(ad::Nil, Imply(PredOf(p, ad), PredOf(p, tFun)))

    val expected = Forall(ad::Nil, Imply(
      Equiv(DifferentialFormula(Forall(x::Nil, pany)), Forall(x::Nil, DifferentialFormula(pany))),
      Equiv(DifferentialFormula(Forall(x::Nil, pany)), Forall(x::Nil, DifferentialFormula(pany)))
    ))

    val result = UniformSubstitutionRule(USubst(substitution), succSeq(f)).apply(succSeq(expected))

    println(result)
  }
}
