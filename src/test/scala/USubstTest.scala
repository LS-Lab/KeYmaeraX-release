import edu.cmu.cs.ls.keymaera.core._
import org.scalatest._
import testHelper.StringConverter
import scala.collection.immutable.{List, Set, Seq}
import StringConverter._

import scala.util.Random

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

object USubstTest extends Tag("USubstTest")

/**
 * @author aplatzer
 * @author smitsch
 */

class USubstTests extends FlatSpec with Matchers {

  "Uniform substitution" should "clash when using vacuous all quantifier for a postcondition x>=0 with a free occurrence of the bound variable" taggedAs(USubstTest) in {
    val x = Variable("x", None, Real)
    val f = GreaterEqual(Real, x, Number(0))
    val p0 = PredicateConstant("p")
      // = Function("p", None, None, Bool) //@TODO check if this is p()
    //@TODO val prem = Axioms.axioms("vacuous all quantifier")
    val prem = Imply(p0, Forall(Seq(x), p0))
    val premseq = Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    val conc = Forall(Seq(x), f)
    val concseq = Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
    val s = Substitution(Seq(SubstitutionPair(p0, f)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitution(s, premseq)(concseq)
  }
  
  it should "clash when using V on x:=x-1 for a postcondition x>=0 with a free occurrence of a bound variable" taggedAs(USubstTest) in {
    val x = Variable("x", None, Real)
    val f = GreaterEqual(Real, x, Number(0))
    val p0 = PredicateConstant("p")
      // = Function("p", None, None, Bool) //@TODO check if this is p()
    val aA = ProgramConstant("a")
    //@TODO val prem = Axioms.axioms("V vacuous")
    val prem = Imply(p0, BoxModality(aA, p0))
    val premseq = Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    val prog = Assign(x, Subtract(Real, x, Number(1)))
    val conc = BoxModality(prog, f)
    val concseq = Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
    val s = Substitution(Seq(SubstitutionPair(p0, f),
      SubstitutionPair(aA, prog)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitution(s, premseq)(concseq)
  }
  
  // uniform substitution of rules
  
  "Uniform substitution of rules" should "instantiate Goedel from (-x)^2>=0" taggedAs(USubstTest) in {
    val x = Variable("x", None, Real)
    val p = Function("p", None, Real, Bool)
    val a = ProgramConstant("a")
    val f = GreaterEqual(Real, Exp(Real, Neg(Real, x), Number(2)), Number(0))
    val fseq = Sequent(Seq(), IndexedSeq(), IndexedSeq(f))
    val prog = Assign(x, Subtract(Real, x, Number(1)))
    val conc = BoxModality(prog, f)
    val concseq = Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))
    val s = Substitution(Seq(SubstitutionPair(ApplyPredicate(p, Anything), f),
      SubstitutionPair(a, prog)))
    AxiomaticRule("Goedel", s)(fseq) should be (concseq)
  }
  
  it should "instantiate Goedel from (-x)^2>=0" in {
    val p = Function("p", None, Real, Bool)
    val a = ProgramConstant("a")
    val f = "(-x)^2>=0".asFormula
    val fseq = Sequent(Seq(), IndexedSeq(), IndexedSeq(f))
    val prog = "x:=x-1;".asProgram
    val s = Substitution(
      SubstitutionPair(ApplyPredicate(p, Anything), f) ::
      SubstitutionPair(a, prog) :: Nil)
    AxiomaticRule("Goedel", s)(fseq) should be (Sequent(Seq(), IndexedSeq(), IndexedSeq(BoxModality(prog, f))))
  }
}