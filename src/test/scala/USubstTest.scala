import edu.cmu.cs.ls.keymaera.core._
import org.scalatest._
import testHelper.StringConverter
import scala.collection.immutable.List
import StringConverter._

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

object USubstTest extends Tag("USubstTest")
object OptimisticTest extends Tag("OptimisticTest")

/**
 * @author aplatzer
 * @author smitsch
 */

class USubstTests extends FlatSpec with Matchers {

  val randomTrials = 40*10
  val randomComplexity = 20
  val rand = new RandomFormula()


  val x = Variable("x", None, Real)
  val z = Variable("z", None, Real)
  val p0 = ApplyPredicate(Function("p", None, Unit, Bool), Nothing)
  val p1 = Function("p", None, Real, Bool)
  val p1_ = Function("p_", None, Real, Bool)
  val pn = Function("p", None, Real, Bool)
  val pn_ = Function("p_", None, Real, Bool)
  val qn = Function("q", None, Real, Bool)
  val qn_ = Function("q_", None, Real, Bool)
  val ap = ProgramConstant("a")
  val ap_ = ProgramConstant("a_")
  //val f1 = Function("f", None, Real, Real)
  val f1_ = Function("f_", None, Real, Real)
  //val g1 = Function("g", None, Real, Real)
  val g1_ = Function("g_", None, Real, Real)

  val ctx  = Function("ctx_", None, Bool, Bool)
  val ctxt = Function("ctx_", None, Real, Real)
  val ctxf = Function("ctx_", None, Real, Bool)

  "Uniform substitution" should "clash when using [:=] for a substitution with a free occurrence of a bound variable" taggedAs USubstTest in {
    val fn = Apply(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      BoxModality("x:=f();".asProgram, ApplyPredicate(p1, "x".asTerm)),
      ApplyPredicate(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=x+1;]x!=x <-> x+1!=x".asFormula
    val s = USubst(Seq(SubstitutionPair(ApplyPredicate(p1, CDot), NotEquals(Real, CDot, "x".asTerm)),
      SubstitutionPair(fn, "x+1".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using [:=] for a substitution with a free occurrence of a bound variable for constants" taggedAs USubstTest in {
    val fn = Apply(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      BoxModality("x:=f();".asProgram, ApplyPredicate(p1, "x".asTerm)),
      ApplyPredicate(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=0;]x=x <-> 0=x".asFormula
    val s = USubst(Seq(SubstitutionPair(ApplyPredicate(p1, CDot), Equals(Real, CDot, "x".asTerm)),
      SubstitutionPair(fn, "0".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }

  /* TODO programs where not all branches write the same variables are not yet supported */
  ignore should "handle nontrivial binding structures" taggedAs USubstTest in {
    val fn = Apply(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      BoxModality("x:=f();".asProgram, ApplyPredicate(p1, "x".asTerm)),
      ApplyPredicate(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=x^2;][{y:=y+1++{z:=x+z;}*}; z:=x+y*z;]y>x <-> [{y:=y+1++{z:=x^2+z;}*}; z:=x^2+y*z;]y>x^2".asFormula

    val y = Variable("y", None, Real)
    val z = Variable("z", None, Real)
    val s = USubst(Seq(
      // [{y:=y+1++{z:=.+z}*}; z:=.+y*z]y>.
      SubstitutionPair(ApplyPredicate(p1, CDot), BoxModality(
        Sequence(
          Choice(
            Assign(y, Add(Real, y, Number(1))),
            Loop(Assign(z, Add(Real, CDot, z)))
          ),
          Assign(z, Add(Real, CDot, Multiply(Real, y, z)))),
        GreaterThan(Real, y, CDot))),
      SubstitutionPair(fn, "x^2".asTerm)))
    UniformSubstitutionRule(s, Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
  }

  it should "clash when using vacuous all quantifier \\forall x . for a postcondition x>=0 with a free occurrence of the bound variable" taggedAs USubstTest in {
    val fml = GreaterEqual(Real, x, Number(0))
    val prem = Axiom.axioms("vacuous all quantifier")
    val conc = Forall(Seq(x), fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
    Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using V on x:=x-1 for a postcondition x>=0 with a free occurrence of a bound variable" taggedAs USubstTest in {
    val fml = GreaterEqual(Real, x, Number(0))
    val prem = Axiom.axioms("V vacuous")
    val prog = Assign(x, Subtract(Real, x, Number(1)))
    val conc = BoxModality(prog, fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml),
      SubstitutionPair(ap, prog)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using \"c()' derive constant fn\" for a substitution with free occurrences" taggedAs USubstTest in {
    val aC = Apply(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x)'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using \"c()' derive constant fn\" for a substitution with free differential occurrences" taggedAs USubstTest in {
    val aC = Apply(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x')'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x'".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }

  // uniform substitution of rules

  "Uniform substitution of rules" should "instantiate Goedel from (-x)^2>=0 (I)" taggedAs USubstTest in {
    val fml = GreaterEqual(Real, Exp(Real, Neg(Real, x), Number(2)), Number(0))
    val prog = Assign(x, Subtract(Real, x, Number(1)))
    val conc = BoxModality(prog, fml)
    val s = USubst(Seq(SubstitutionPair(ApplyPredicate(p1_, Anything), fml),
      SubstitutionPair(ap_, prog)))
    AxiomaticRule("Goedel", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate Goedel from (-x)^2>=0 (II)" taggedAs USubstTest in {
    val fml = "(-x)^2>=0".asFormula
    val prog = "x:=x-1;".asProgram
    val s = USubst(
      SubstitutionPair(ApplyPredicate(p1_, Anything), fml) ::
      SubstitutionPair(ap_, prog) :: Nil)
    AxiomaticRule("Goedel", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(BoxModality(prog, fml)))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate nontrivial binding structures in [] congruence" taggedAs USubstTest in {
      val prem = "(-x)^2>=y <-> x^2>=y".asFormula
      val conc = "[{y:=y+1++{z:=x+z;}*}; z:=x+y*z;](-x)^2>=y <-> [{y:=y+1++{z:=x+z;}*}; z:=x+y*z;]x^2>=y".asFormula

      val prog = "{y:=y+1++{z:=x+z;}*}; z:=x+y*z;".asProgram
      val q_ = Function("q_", None, Real, Bool)
      val s = USubst(Seq(
        SubstitutionPair(ap_, prog),
        SubstitutionPair(ApplyPredicate(pn_, Anything), "(-x)^2>=y".asFormula),
        SubstitutionPair(ApplyPredicate(q_, Anything), "x^2>=y".asFormula)
         ))
        AxiomaticRule("[] congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
    }

    it should "instantiate random programs in [] monotone" taggedAs USubstTest in {
      for (i <- 1 to randomTrials) {
        val prem1 = "(-z1)^2>=z4".asFormula
        val prem2 = "z4<=z1^2".asFormula
        val prog = rand.nextProgram(randomComplexity)
        val concLhs = BoxModality(prog, prem1)
        val concRhs = BoxModality(prog, prem2)
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(ApplyPredicate(pn_, Anything), prem1),
          SubstitutionPair(ApplyPredicate(q_, Anything), prem2)
           ))
          AxiomaticRule("[] monotone", s)(Sequent(Seq(), IndexedSeq(concLhs), IndexedSeq(concRhs))) should contain only
            Sequent(Seq(), IndexedSeq(prem1), IndexedSeq(prem2))
      }
    }

    it should "instantiate random programs in [] congruence" taggedAs USubstTest in {
      for (i <- 1 to randomTrials) {
        val prem1 = "(-z1)^2>=z4".asFormula
        val prem2 = "z4<=z1^2".asFormula
        val prem = Equiv(prem1, prem2)
        val prog = rand.nextProgram(randomComplexity)
        val conc = Equiv(BoxModality(prog, prem1), BoxModality(prog, prem2))
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(ApplyPredicate(pn_, Anything), prem1),
          SubstitutionPair(ApplyPredicate(q_, Anything), prem2)
           ))
          AxiomaticRule("[] congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
      }
    }

    it should "instantiate random programs in <> congruence" taggedAs USubstTest in {
      for (i <- 1 to randomTrials) {
        val prem1 = "(-z1)^2>=z4".asFormula
        val prem2 = "z4<=z1^2".asFormula
        val prem = Equiv(prem1, prem2)
        val prog = rand.nextProgram(randomComplexity)
        val conc = Equiv(DiamondModality(prog, prem1), DiamondModality(prog, prem2))
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(ApplyPredicate(pn_, Anything), prem1),
          SubstitutionPair(ApplyPredicate(q_, Anything), prem2)
           ))
          AxiomaticRule("<> congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
      }
    }

    it should "instantiate random programs in <> monotone" taggedAs USubstTest in {
      for (i <- 1 to randomTrials) {
        val prem1 = "(-z1)^2>=z4".asFormula
        val prem2 = "z4<=z1^2".asFormula
        val prog = rand.nextProgram(randomComplexity)
        val concLhs = DiamondModality(prog, prem1)
        val concRhs = DiamondModality(prog, prem2)
        println("Random precontext " + prog.prettyString)

        val q_ = Function("q_", None, Real, Bool)
        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(ApplyPredicate(pn_, Anything), prem1),
          SubstitutionPair(ApplyPredicate(q_, Anything), prem2)
           ))
          AxiomaticRule("<> monotone", s)(
            Sequent(Seq(), IndexedSeq(concLhs), IndexedSeq(concRhs))) should contain only Sequent(Seq(), IndexedSeq(prem1), IndexedSeq(prem2))
      }
    }

    it should "instantiate random programs in Goedel" taggedAs USubstTest in {
      for (i <- 1 to randomTrials) {
        val prem = "(-z1)^2>=0".asFormula
        val prog = rand.nextProgram(randomComplexity)
        val conc = BoxModality(prog, prem)
        println("Random precontext " + prog.prettyString)

        val s = USubst(Seq(
          SubstitutionPair(ap_, prog),
          SubstitutionPair(ApplyPredicate(pn_, Anything), prem)
           ))
          AxiomaticRule("Goedel", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
      }
    }

  "Congruence rules" should "instantiate CT from y+z=z+y" taggedAs USubstTest in {
        val term1 = "y+z".asTerm
        val term2 = "z+y".asTerm
        val fml = Equals(Real, term1, term2)
        val s = USubst(
          SubstitutionPair(Apply(f1_, Anything), term1) ::
          SubstitutionPair(Apply(g1_, Anything), term2) ::
          SubstitutionPair(Apply(ctxt, CDot), Subtract(Real, CDot, Number(5))) :: Nil)
        AxiomaticRule("CT term congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, Subtract(Real, term1, Number(5)),
          Subtract(Real, term2, Number(5)))))
          ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
    
    it should "instantiate CT from y+z=z+y in more context" taggedAs USubstTest in {
        val term1 = "y+z".asTerm
        val term2 = "z+y".asTerm
        val fml = Equals(Real, term1, term2)
        val s = USubst(
          SubstitutionPair(Apply(f1_, Anything), term1) ::
          SubstitutionPair(Apply(g1_, Anything), term2) ::
          SubstitutionPair(Apply(ctxt, CDot), Multiply(Real, Exp(Real, x, Number(3)), CDot)) :: Nil)
        AxiomaticRule("CT term congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, Multiply(Real, Exp(Real, x, Number(3)), term1),
          Multiply(Real, Exp(Real, x, Number(3)), term2))
          ))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
    
      it should "instantiate CT from y+z=z+y in random context" taggedAs USubstTest in {
        for (i <- 1 to randomTrials) {
          val term1 = "y+z".asTerm
          val term2 = "z+y".asTerm
          val fml = Equals(Real, term1, term2)
          val context = rand.nextDotTerm(randomComplexity)
          println("Random context " + context.prettyString)
          val s = USubst(
            SubstitutionPair(Apply(f1_, Anything), term1) ::
            SubstitutionPair(Apply(g1_, Anything), term2) ::
            SubstitutionPair(Apply(ctxt, CDot), context) :: Nil)
          AxiomaticRule("CT term congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, contextapp(context, term1), contextapp(context, term2))))
            ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
      }

      it should "instantiate CT from z1+z3*z2=z2*z3+z1 in random context" taggedAs USubstTest in {
        for (i <- 1 to randomTrials) {
          val term1 = "z1+z3*z2".asTerm
          val term2 = "z2*z3+z1".asTerm
          val fml = Equals(Real, term1, term2)
          val context = rand.nextDotTerm(randomComplexity)
          println("Random context " + context.prettyString)
          val s = USubst(
            SubstitutionPair(Apply(f1_, Anything), term1) ::
            SubstitutionPair(Apply(g1_, Anything), term2) ::
            SubstitutionPair(Apply(ctxt, CDot), context) :: Nil)
          AxiomaticRule("CT term congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, contextapp(context, term1), contextapp(context, term2))))
            ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
      }

    it should "instantiate CT from z1*z3-z2=z2-z4/z1 in random context" taggedAs USubstTest in {
        for (i <- 1 to randomTrials) {
          val term1 = "z1*z3-z2".asTerm
          val term2 = "z2-z4/z1".asTerm
          val fml = Equals(Real, term1, term2)
          val context = rand.nextDotTerm(randomComplexity)
          println("Random context " + context.prettyString)
          val s = USubst(
            SubstitutionPair(Apply(f1_, Anything), term1) ::
            SubstitutionPair(Apply(g1_, Anything), term2) ::
            SubstitutionPair(Apply(ctxt, CDot), context) :: Nil)
          AxiomaticRule("CT term congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, contextapp(context, term1), contextapp(context, term2))))
            ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
      }

    it should "instantiate CQ from y+z=z+y in context y>1&.<=5" taggedAs USubstTest in {
          val term1 = "y+z".asTerm
          val term2 = "z+y".asTerm
          val fml = Equals(Real, term1, term2)
          val y = Variable("y", None, Real)
          val s = USubst(
            SubstitutionPair(Apply(f1_, Anything), term1) ::
            SubstitutionPair(Apply(g1_, Anything), term2) ::
            SubstitutionPair(ApplyPredicate(ctxf, CDot), And(GreaterThan(Real, y, Number(1)), LessEqual(Real, CDot, Number(5)))) :: Nil)
          AxiomaticRule("CQ equation congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( And(GreaterThan(Real, y, Number(1)), LessEqual(Real, term1, Number(5))),
            And(GreaterThan(Real, y, Number(1)), LessEqual(Real, term2, Number(5)))
            )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
        
        it should "instantiate CQ from y+z=z+y in context \\forall x .<=5" taggedAs USubstTest in {
              val term1 = "y+z".asTerm
              val term2 = "z+y".asTerm
              val fml = Equals(Real, term1, term2)
              val y = Variable("x", None, Real)
              val s = USubst(
                SubstitutionPair(Apply(f1_, Anything), term1) ::
                SubstitutionPair(Apply(g1_, Anything), term2) ::
                SubstitutionPair(ApplyPredicate(ctxf, CDot), Forall(Seq(y),  LessEqual(Real, CDot, Number(5)))) :: Nil)
              AxiomaticRule("CQ equation congruence", s)(
                Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(Real, term1, Number(5))),
                Forall(Seq(y),  LessEqual(Real, term2, Number(5)))
                )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
            }

        ignore should "?instantiate CQ from y+z=z+y in context \\forall y .<=5" taggedAs OptimisticTest in {
              val term1 = "y+z".asTerm
              val term2 = "z+y".asTerm
              val fml = Equals(Real, term1, term2)
              val y = Variable("y", None, Real)
              val s = USubst(
                SubstitutionPair(Apply(f1_, Anything), term1) ::
                SubstitutionPair(Apply(g1_, Anything), term2) ::
                SubstitutionPair(ApplyPredicate(ctxf, CDot), Forall(Seq(y),  LessEqual(Real, CDot, Number(5)))) :: Nil)
              AxiomaticRule("CQ equation congruence", s)(
                Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(Real, term1, Number(5))),
                Forall(Seq(y),  LessEqual(Real, term2, Number(5)))
                )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
            }

            it should "instantiate CQ from y+z=z+y in context [x:=x-1]" taggedAs USubstTest in {
              val term1 = "y+z".asTerm
              val term2 = "z+y".asTerm
                val fml = Equals(Real, term1, term2)
                val prog = "x:=x-1;".asProgram
                val s = USubst(
                  SubstitutionPair(Apply(f1_, Anything), term1) ::
                  SubstitutionPair(Apply(g1_, Anything), term2) ::
                  SubstitutionPair(ApplyPredicate(ctxf, CDot), Modality(BoxModality(prog), GreaterEqual(Real, CDot, Number(0)))) :: Nil)
                AxiomaticRule("CQ equation congruence", s)(
                  Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Modality(BoxModality(prog), GreaterEqual(Real, term1, Number(0))),
                  Modality(BoxModality(prog), GreaterEqual(Real, term2, Number(0)))
                  )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
              }

  ignore should "?instantiate CQ from y+z=z+y in context [y:=y-1]" taggedAs OptimisticTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
      val fml = Equals(Real, term1, term2)
      val prog = "y:=y-1;".asProgram
      val s = USubst(
        SubstitutionPair(Apply(f1_, Anything), term1) ::
        SubstitutionPair(Apply(g1_, Anything), term2) ::
        SubstitutionPair(ApplyPredicate(ctxf, CDot), Modality(BoxModality(prog), GreaterEqual(Real, CDot, Number(0)))) :: Nil)
      AxiomaticRule("CQ equation congruence", s)(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Modality(BoxModality(prog), GreaterEqual(Real, term1, Number(0))),
        Modality(BoxModality(prog), GreaterEqual(Real, term2, Number(0)))
        )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }


  it should "instantiate CT from z^2*y=-(-z)^2*-y+0" taggedAs USubstTest in {
        val term1 = "z^2*y".asTerm
        val term2 = "-(-z)^2*-y+0".asTerm
        val fml = Equals(Real, term1, term2)
        val s = USubst(
          SubstitutionPair(Apply(f1_, Anything), term1) ::
          SubstitutionPair(Apply(g1_, Anything), term2) ::
          SubstitutionPair(Apply(ctxt, CDot), Multiply(Real, Exp(Real, x, Number(3)), CDot)) :: Nil)
        AxiomaticRule("CT term congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equals(Real, Multiply(Real, Exp(Real, x, Number(3)), term1),
          Multiply(Real, Exp(Real, x, Number(3)), term2))
          ))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
    
      ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context \\forall y" taggedAs OptimisticTest in {
          val term1 = "z^2*y".asTerm
          val term2 = "-(-z)^2*-y+0".asTerm
          val fml = Equals(Real, term1, term2)
          val y = Variable("y", None, Real)
          val s = USubst(
            SubstitutionPair(Apply(f1_, Anything), term1) ::
            SubstitutionPair(Apply(g1_, Anything), term2) ::
            SubstitutionPair(ApplyPredicate(ctxf, CDot), Forall(Seq(y), GreaterEqual(Real, CDot, Number(0)))) :: Nil)
          AxiomaticRule("CQ equation congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y), GreaterEqual(Real, term1, Number(0))),
            Forall(Seq(y), GreaterEqual(Real, term2, Number(0)))
            )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
  
    ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context [y:=y-1]" taggedAs OptimisticTest in {
        val term1 = "z^2*y".asTerm
        val term2 = "-(-z)^2*-y+0".asTerm
        val fml = Equals(Real, term1, term2)
        val prog = "y:=y-1;".asProgram
        val s = USubst(
          SubstitutionPair(Apply(f1_, Anything), term1) ::
          SubstitutionPair(Apply(g1_, Anything), term2) ::
          SubstitutionPair(ApplyPredicate(ctxf, CDot), Modality(BoxModality(prog), GreaterEqual(Real, CDot, Number(0)))) :: Nil)
        AxiomaticRule("CQ equation congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Modality(BoxModality(prog), GreaterEqual(Real, term1, Number(0))),
          Modality(BoxModality(prog), GreaterEqual(Real, term2, Number(0)))
          )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
  
  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (manual test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), CDotFormula)
    val s = USubst(
      SubstitutionPair(ApplyPredicate(pn_, Anything), fml1) ::
      SubstitutionPair(ApplyPredicate(qn_, Anything), fml2) ::
      SubstitutionPair(ApplyPredicational(ctx, CDotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (schematic test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), CDotFormula)
    val s = USubst(
      SubstitutionPair(ApplyPredicate(pn_, Anything), fml1) ::
      SubstitutionPair(ApplyPredicate(qn_, Anything), fml2) ::
      SubstitutionPair(ApplyPredicational(ctx, CDotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(x), fml1), Forall(Seq(x), fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CE from x=0 <-> x^2=0 into [x:=5] context (schematic test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "x:=5;".asProgram
    val context = Modality(BoxModality(prog), CDotFormula)
    val s = USubst(
      SubstitutionPair(ApplyPredicate(pn_, Anything), fml1) ::
      SubstitutionPair(ApplyPredicate(qn_, Anything), fml2) ::
      SubstitutionPair(ApplyPredicational(ctx, CDotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Modality(BoxModality(prog), fml1), Modality(BoxModality(prog), fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into [x'=5] context (schematic test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "x'=5;".asProgram  //ODESystem(Seq(), AtomicODE(Derivative(Real, x), Number(5)), True)
    val context = Modality(BoxModality(prog), CDotFormula)
    val s = USubst(
      SubstitutionPair(ApplyPredicate(pn_, Anything), fml1) ::
      SubstitutionPair(ApplyPredicate(qn_, Anything), fml2) ::
      SubstitutionPair(ApplyPredicational(ctx, CDotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Modality(BoxModality(prog), fml1), Modality(BoxModality(prog), fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in complex contexts" taggedAs OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equals(Real, term1, term2)
    val prog = "y:=y-1;{z:=-z+2++z:=0}".asProgram
    val u = Variable("u", None, Real)
    val s = USubst(
      SubstitutionPair(Apply(f1_, Anything), term1) ::
      SubstitutionPair(Apply(g1_, Anything), term2) ::
      SubstitutionPair(ApplyPredicate(ctxf, CDot), Forall(Seq(u), Modality(BoxModality(prog), GreaterEqual(Real, CDot, u)))) :: Nil)
    AxiomaticRule("CQ equation congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(u), Modality(BoxModality(prog), GreaterEqual(Real, term1, u))),
      Forall(Seq(u), Modality(BoxModality(prog), GreaterEqual(Real, term2, u)))
      )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
     }
  
   it should "instantiate CQ from z^2*y=-(-z)^2*-y+0 in random contexts" taggedAs USubstTest in {
       val term1 = "z^2*y".asTerm
       val term2 = "-(-z)^2*-y+0".asTerm
       val fml = Equals(Real, term1, term2)
       val context = rand.nextDotFormula(randomComplexity)
       println("Random context " + context.prettyString)
       val s = USubst(
         SubstitutionPair(Apply(f1_, Anything), term1) ::
         SubstitutionPair(Apply(g1_, Anything), term2) ::
         SubstitutionPair(ApplyPredicate(ctxf, CDot), context) :: Nil)
       AxiomaticRule("CQ equation congruence", s)(
         Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, term1), contextapp(context, term2))))
         ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CE from z^2*y>=5 <-> (-z)^2*-y+0<=-5 in random contexts" taggedAs USubstTest in {
      val fml1 = "z^2*y>=5".asFormula
      val fml2 = "(-z)^2*-y+0<=-5".asFormula
      val fml = Equiv(fml1, fml2)
      val context = rand.nextDotFormula(randomComplexity)
      println("Random context " + context.prettyString)
      val s = USubst(
        SubstitutionPair(ApplyPredicate(pn_, Anything), fml1) ::
        SubstitutionPair(ApplyPredicate(qn_, Anything), fml2) ::
        SubstitutionPair(ApplyPredicational(ctx, CDotFormula), context) :: Nil)
      AxiomaticRule("CE congruence", s)(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
        ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
 }

 // apply given context to the given argument
  def contextapp(context: Term, arg: Term) : Term =
   USubst(SubstitutionPair(CDot, arg) :: Nil)(context)

  def contextapp(context: Formula, arg: Term) : Formula =
    USubst(SubstitutionPair(CDot, arg) :: Nil)(context)
  
  def contextapp(context: Formula, arg: Formula) : Formula = {
    val mycontext = Function("dottingC__", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC__", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype

    USubst(SubstitutionPair(ApplyPredicational(mycontext, CDotFormula), context) :: Nil)(ApplyPredicational(mycontext, arg))
  }
}