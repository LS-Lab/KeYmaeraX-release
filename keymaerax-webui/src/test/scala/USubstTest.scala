import edu.cmu.cs.ls.keymaerax.core._
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
  val p0 = PredOf(Function("p", None, Unit, Bool), Nothing)
  val p1 = Function("p", None, Real, Bool)
  val p1_ = Function("p_", None, Real, Bool)
  val pn = Function("p", None, Real, Bool)
  val pn_ = Function("p_", None, Real, Bool)
  val qn = Function("q", None, Real, Bool)
  val qn_ = Function("q_", None, Real, Bool)
  val ap = ProgramConst("a")
  val ap_ = ProgramConst("a_")
  //val f1 = Function("f", None, Real, Real)
  val f1_ = Function("f_", None, Real, Real)
  //val g1 = Function("g", None, Real, Real)
  val g1_ = Function("g_", None, Real, Real)

  val ctx  = Function("ctx_", None, Bool, Bool)
  val ctxt = Function("ctx_", None, Real, Real)
  val ctxf = Function("ctx_", None, Real, Bool)

  "Uniform substitution" should "substitute simple formula p(x) <-> ! ! p(- - x)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    // p(x) <-> ! ! p(- - x)
    val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
    s(prem) should be ("x^5>=0 <-> !(!((-(-x))^5>=0))".asFormula)
  }

  it should "substitute simple sequent p(x) <-> ! ! p(- - x)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    // p(x) <-> ! ! p(- - x)
    val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
    val conc = "x^5>=0 <-> !(!((-(-x))^5>=0))".asFormula
    UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be
    (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
  }

  it should "substitute simple formula [a]p(x) <-> [a](p(x)&true)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    val a = ProgramConst("a")
    // [a]p(x) <-> [a](p(x)&true)
    val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
      SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
    s(prem) should be ("[x'=5;]x>=2 <-> [x'=5;](x>=2&true)".asFormula)
  }

  it should "substitute simple sequent [a]p(x) <-> [a](p(x)&true)" in {
    val p = Function("p", None, Real, Bool)
    val x = Variable("x", None, Real)
    val a = ProgramConst("a")
    // [a]p(x) <-> [a](p(x)&true)
    val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
    val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
      SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
    val conc = "[x'=5;]x>=2 <-> [x'=5;](x>=2&true)".asFormula
    UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be
    (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
  }


  it should "clash when using [:=] for a substitution with a free occurrence of a bound variable" taggedAs USubstTest in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=x+1;]x!=x <-> x+1!=x".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), NotEqual(DotTerm, "x".asTerm)),
      SubstitutionPair(fn, "x+1".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using [:=] for a substitution with a free occurrence of a bound variable for constants" taggedAs USubstTest in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=0;]x=x <-> 0=x".asFormula
    val s = USubst(Seq(SubstitutionPair(PredOf(p1, DotTerm), Equal(DotTerm, "x".asTerm)),
      SubstitutionPair(fn, "0".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }

  /* TODO programs where not all branches write the same variables are not yet supported */
  ignore should "handle nontrivial binding structures" taggedAs USubstTest in {
    val fn = FuncOf(Function("f", None, Unit, Real), Nothing)
    val prem = Equiv(
      Box("x:=f();".asProgram, PredOf(p1, "x".asTerm)),
      PredOf(p1, fn)) // axioms.axiom("[:=])
    val conc = "[x:=x^2;][{y:=y+1++{z:=x+z;}*}; z:=x+y*z;]y>x <-> [{y:=y+1++{z:=x^2+z;}*}; z:=x^2+y*z;]y>x^2".asFormula

    val y = Variable("y", None, Real)
    val z = Variable("z", None, Real)
    val s = USubst(Seq(
      // [{y:=y+1++{z:=.+z}*}; z:=.+y*z]y>.
      SubstitutionPair(PredOf(p1, DotTerm), Box(
        Compose(
          Choice(
            Assign(y, Plus(y, Number(1))),
            Loop(Assign(z, Plus(DotTerm, z)))
          ),
          Assign(z, Plus(DotTerm, Times(y, z)))),
        Greater(y, DotTerm))),
      SubstitutionPair(fn, "x^2".asTerm)))
    UniformSubstitutionRule(s, Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
  }

  it should "clash when using vacuous all quantifier \\forall x . for a postcondition x>=0 with a free occurrence of the bound variable" taggedAs USubstTest in {
    val fml = GreaterEqual(x, Number(0))
    val prem = Axiom.axioms("vacuous all quantifier")
    val conc = Forall(Seq(x), fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
    Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using V on x:=x-1 for a postcondition x>=0 with a free occurrence of a bound variable" taggedAs USubstTest in {
    val fml = GreaterEqual(x, Number(0))
    val prem = Axiom.axioms("V vacuous")
    val prog = Assign(x, Minus(x, Number(1)))
    val conc = Box(prog, fml)
    val s = USubst(Seq(SubstitutionPair(p0, fml),
      SubstitutionPair(ap, prog)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using \"c()' derive constant fn\" for a substitution with free occurrences" taggedAs USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x)'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }
  
  it should "clash when using \"c()' derive constant fn\" for a substitution with free differential occurrences" taggedAs USubstTest in {
    val aC = FuncOf(Function("c", None, Unit, Real), Nothing)
    val prem = "(c())'=0".asFormula // axioms.axiom("c()' derive constant fn")
    val conc = "(x')'=0".asFormula
    val s = USubst(Seq(SubstitutionPair(aC, "x'".asTerm)))
    a [SubstitutionClashException] should be thrownBy UniformSubstitutionRule(s,
      Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
  }

  // uniform substitution of rules

  "Uniform substitution of rules" should "instantiate Goedel from (-x)^2>=0 (I)" taggedAs USubstTest in {
    val fml = GreaterEqual(Power(Neg(x), Number(2)), Number(0))
    val prog = Assign(x, Minus(x, Number(1)))
    val conc = Box(prog, fml)
    val s = USubst(Seq(SubstitutionPair(PredOf(p1_, Anything), fml),
      SubstitutionPair(ap_, prog)))
    AxiomaticRule("Goedel", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate Goedel from (-x)^2>=0 (II)" taggedAs USubstTest in {
    val fml = "(-x)^2>=0".asFormula
    val prog = "x:=x-1;".asProgram
    val s = USubst(
      SubstitutionPair(PredOf(p1_, Anything), fml) ::
      SubstitutionPair(ap_, prog) :: Nil)
    AxiomaticRule("Goedel", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Box(prog, fml)))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate nontrivial binding structures in [] congruence" taggedAs USubstTest in {
    val prem = "(-x)^2>=y <-> x^2>=y".asFormula
    val conc = "[{y:=y+1++{z:=x+z;}*}; z:=x+y*z;](-x)^2>=y <-> [{y:=y+1++{z:=x+z;}*}; z:=x+y*z;]x^2>=y".asFormula

    val prog = "{y:=y+1++{z:=x+z;}*}; z:=x+y*z;".asProgram
    val q_ = Function("q_", None, Real, Bool)
    val ctx_ = Function("ctx_", None, Bool, Bool)
    val s = USubst(
      SubstitutionPair(ap_, prog) ::
      SubstitutionPair(PredOf(pn_, Anything), "(-x)^2>=y".asFormula) ::
      SubstitutionPair(PredOf(q_, Anything), "x^2>=y".asFormula) ::
      SubstitutionPair(PredicationalOf(ctx_, DotFormula), Box("{y:=y+1++{z:=x+z;}*}; z:=x+y*z;".asProgram, DotFormula)) :: Nil)
      AxiomaticRule("CE congruence", s)(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))))
  }

  it should "instantiate random programs in [] monotone" taggedAs USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val concLhs = Box(prog, prem1)
      val concRhs = Box(prog, prem2)
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val s = USubst(Seq(
        SubstitutionPair(ap_, prog),
        SubstitutionPair(PredOf(pn_, Anything), prem1),
        SubstitutionPair(PredOf(q_, Anything), prem2)
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
      val conc = Equiv(Box(prog, prem1), Box(prog, prem2))
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val ctx_ = Function("ctx_", None, Bool, Bool)

      val s = USubst(SubstitutionPair(ap_, prog) ::
        SubstitutionPair(PredOf(pn_, Anything), prem1) ::
        SubstitutionPair(PredOf(q_, Anything), prem2) ::
        SubstitutionPair(PredicationalOf(ctx_, DotFormula), Box(prog, DotFormula)) :: Nil)
      AxiomaticRule("CE congruence", s)(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    }
  }

  it should "instantiate random programs in <> congruence" taggedAs USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prem = Equiv(prem1, prem2)
      val prog = rand.nextProgram(randomComplexity)
      val conc = Equiv(Diamond(prog, prem1), Diamond(prog, prem2))
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val ctx_ = Function("ctx_", None, Bool, Bool)

      val s = USubst(SubstitutionPair(ap_, prog) ::
        SubstitutionPair(PredOf(pn_, Anything), prem1) ::
        SubstitutionPair(PredOf(q_, Anything), prem2) ::
        SubstitutionPair(PredicationalOf(ctx_, DotFormula), Diamond(prog, DotFormula)) :: Nil)
      AxiomaticRule("CE congruence", s)(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    }
  }

  it should "instantiate random programs in <> monotone" taggedAs USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem1 = "(-z1)^2>=z4".asFormula
      val prem2 = "z4<=z1^2".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val concLhs = Diamond(prog, prem1)
      val concRhs = Diamond(prog, prem2)
      println("Random precontext " + prog.prettyString)

      val q_ = Function("q_", None, Real, Bool)
      val s = USubst(Seq(
        SubstitutionPair(ap_, prog),
        SubstitutionPair(PredOf(pn_, Anything), prem1),
        SubstitutionPair(PredOf(q_, Anything), prem2)
         ))
        AxiomaticRule("<> monotone", s)(
          Sequent(Seq(), IndexedSeq(concLhs), IndexedSeq(concRhs))) should contain only Sequent(Seq(), IndexedSeq(prem1), IndexedSeq(prem2))
    }
  }

  it should "instantiate random programs in Goedel" taggedAs USubstTest in {
    for (i <- 1 to randomTrials) {
      val prem = "(-z1)^2>=0".asFormula
      val prog = rand.nextProgram(randomComplexity)
      val conc = Box(prog, prem)
      println("Random precontext " + prog.prettyString)

      val s = USubst(Seq(
        SubstitutionPair(ap_, prog),
        SubstitutionPair(PredOf(pn_, Anything), prem)
         ))
        AxiomaticRule("Goedel", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(conc))) should contain only Sequent(Seq(), IndexedSeq(), IndexedSeq(prem))
    }
  }

  "Congruence rules" should "instantiate CT from y+z=z+y" taggedAs USubstTest in {
        val term1 = "y+z".asTerm
        val term2 = "z+y".asTerm
        val fml = Equal(term1, term2)
        val s = USubst(
          SubstitutionPair(FuncOf(f1_, Anything), term1) ::
          SubstitutionPair(FuncOf(g1_, Anything), term2) ::
          SubstitutionPair(FuncOf(ctxt, DotTerm), Minus(DotTerm, Number(5))) :: Nil)
        AxiomaticRule("CT term congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(Minus(term1, Number(5)),
          Minus(term2, Number(5)))))
          ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
    
    it should "instantiate CT from y+z=z+y in more context" taggedAs USubstTest in {
        val term1 = "y+z".asTerm
        val term2 = "z+y".asTerm
        val fml = Equal(term1, term2)
        val s = USubst(
          SubstitutionPair(FuncOf(f1_, Anything), term1) ::
          SubstitutionPair(FuncOf(g1_, Anything), term2) ::
          SubstitutionPair(FuncOf(ctxt, DotTerm), Times(Power(x, Number(3)), DotTerm)) :: Nil)
        AxiomaticRule("CT term congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(Times(Power(x, Number(3)), term1),
          Times(Power(x, Number(3)), term2))
          ))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
    
      it should "instantiate CT from y+z=z+y in random context" taggedAs USubstTest in {
        for (i <- 1 to randomTrials) {
          val term1 = "y+z".asTerm
          val term2 = "z+y".asTerm
          val fml = Equal(term1, term2)
          val context = rand.nextDotTerm(randomComplexity)
          println("Random context " + context.prettyString)
          val s = USubst(
            SubstitutionPair(FuncOf(f1_, Anything), term1) ::
            SubstitutionPair(FuncOf(g1_, Anything), term2) ::
            SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
          AxiomaticRule("CT term congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
            ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
      }

      it should "instantiate CT from z1+z3*z2=z2*z3+z1 in random context" taggedAs USubstTest in {
        for (i <- 1 to randomTrials) {
          val term1 = "z1+z3*z2".asTerm
          val term2 = "z2*z3+z1".asTerm
          val fml = Equal(term1, term2)
          val context = rand.nextDotTerm(randomComplexity)
          println("Random context " + context.prettyString)
          val s = USubst(
            SubstitutionPair(FuncOf(f1_, Anything), term1) ::
            SubstitutionPair(FuncOf(g1_, Anything), term2) ::
            SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
          AxiomaticRule("CT term congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
            ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
      }

    it should "instantiate CT from z1*z3-z2=z2-z4/z1 in random context" taggedAs USubstTest in {
        for (i <- 1 to randomTrials) {
          val term1 = "z1*z3-z2".asTerm
          val term2 = "z2-z4/z1".asTerm
          val fml = Equal(term1, term2)
          val context = rand.nextDotTerm(randomComplexity)
          println("Random context " + context.prettyString)
          val s = USubst(
            SubstitutionPair(FuncOf(f1_, Anything), term1) ::
            SubstitutionPair(FuncOf(g1_, Anything), term2) ::
            SubstitutionPair(FuncOf(ctxt, DotTerm), context) :: Nil)
          AxiomaticRule("CT term congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(contextapp(context, term1), contextapp(context, term2))))
            ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
      }

    it should "instantiate CQ from y+z=z+y in context y>1&.<=5" taggedAs USubstTest in {
          val term1 = "y+z".asTerm
          val term2 = "z+y".asTerm
          val fml = Equal(term1, term2)
          val y = Variable("y", None, Real)
          val s = USubst(
            SubstitutionPair(FuncOf(f1_, Anything), term1) ::
            SubstitutionPair(FuncOf(g1_, Anything), term2) ::
            SubstitutionPair(PredOf(ctxf, DotTerm), And(Greater(y, Number(1)), LessEqual(DotTerm, Number(5)))) :: Nil)
          AxiomaticRule("CQ equation congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( And(Greater(y, Number(1)), LessEqual(term1, Number(5))),
            And(Greater(y, Number(1)), LessEqual(term2, Number(5)))
            )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
        
        it should "instantiate CQ from y+z=z+y in context \\forall x .<=5" taggedAs USubstTest in {
              val term1 = "y+z".asTerm
              val term2 = "z+y".asTerm
              val fml = Equal(term1, term2)
              val y = Variable("x", None, Real)
              val s = USubst(
                SubstitutionPair(FuncOf(f1_, Anything), term1) ::
                SubstitutionPair(FuncOf(g1_, Anything), term2) ::
                SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y),  LessEqual(DotTerm, Number(5)))) :: Nil)
              AxiomaticRule("CQ equation congruence", s)(
                Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(term1, Number(5))),
                Forall(Seq(y),  LessEqual(term2, Number(5)))
                )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
            }

        ignore should "?instantiate CQ from y+z=z+y in context \\forall y .<=5" taggedAs OptimisticTest in {
              val term1 = "y+z".asTerm
              val term2 = "z+y".asTerm
              val fml = Equal(term1, term2)
              val y = Variable("y", None, Real)
              val s = USubst(
                SubstitutionPair(FuncOf(f1_, Anything), term1) ::
                SubstitutionPair(FuncOf(g1_, Anything), term2) ::
                SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y),  LessEqual(DotTerm, Number(5)))) :: Nil)
              AxiomaticRule("CQ equation congruence", s)(
                Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y),  LessEqual(term1, Number(5))),
                Forall(Seq(y),  LessEqual(term2, Number(5)))
                )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
            }

            it should "instantiate CQ from y+z=z+y in context [x:=x-1]" taggedAs USubstTest in {
              val term1 = "y+z".asTerm
              val term2 = "z+y".asTerm
                val fml = Equal(term1, term2)
                val prog = "x:=x-1;".asProgram
                val s = USubst(
                  SubstitutionPair(FuncOf(f1_, Anything), term1) ::
                  SubstitutionPair(FuncOf(g1_, Anything), term2) ::
                  SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
                AxiomaticRule("CQ equation congruence", s)(
                  Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Box(prog, GreaterEqual(term1, Number(0))),
                  Box(prog, GreaterEqual(term2, Number(0)))
                  )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
              }

  ignore should "?instantiate CQ from y+z=z+y in context [y:=y-1]" taggedAs OptimisticTest in {
    val term1 = "y+z".asTerm
    val term2 = "z+y".asTerm
      val fml = Equal(term1, term2)
      val prog = "y:=y-1;".asProgram
      val s = USubst(
        SubstitutionPair(FuncOf(f1_, Anything), term1) ::
        SubstitutionPair(FuncOf(g1_, Anything), term2) ::
        SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
      AxiomaticRule("CQ equation congruence", s)(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, GreaterEqual(term1, Number(0))),
        Box(prog, GreaterEqual(term2, Number(0)))
        )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
    }


  it should "instantiate CT from z^2*y=-(-z)^2*-y+0" taggedAs USubstTest in {
        val term1 = "z^2*y".asTerm
        val term2 = "-(-z)^2*-y+0".asTerm
        val fml = Equal(term1, term2)
        val s = USubst(
          SubstitutionPair(FuncOf(f1_, Anything), term1) ::
          SubstitutionPair(FuncOf(g1_, Anything), term2) ::
          SubstitutionPair(FuncOf(ctxt, DotTerm), Times(Power(x, Number(3)), DotTerm)) :: Nil)
        AxiomaticRule("CT term congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equal(Times(Power(x, Number(3)), term1),
          Times(Power(x, Number(3)), term2))
          ))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
    
      ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context \\forall y" taggedAs OptimisticTest in {
          val term1 = "z^2*y".asTerm
          val term2 = "-(-z)^2*-y+0".asTerm
          val fml = Equal(term1, term2)
          val y = Variable("y", None, Real)
          val s = USubst(
            SubstitutionPair(FuncOf(f1_, Anything), term1) ::
            SubstitutionPair(FuncOf(g1_, Anything), term2) ::
            SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(y), GreaterEqual(DotTerm, Number(0)))) :: Nil)
          AxiomaticRule("CQ equation congruence", s)(
            Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv( Forall(Seq(y), GreaterEqual(term1, Number(0))),
            Forall(Seq(y), GreaterEqual(term2, Number(0)))
            )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
        }
  
    ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in context [y:=y-1]" taggedAs OptimisticTest in {
        val term1 = "z^2*y".asTerm
        val term2 = "-(-z)^2*-y+0".asTerm
        val fml = Equal(term1, term2)
        val prog = "y:=y-1;".asProgram
        val s = USubst(
          SubstitutionPair(FuncOf(f1_, Anything), term1) ::
          SubstitutionPair(FuncOf(g1_, Anything), term2) ::
          SubstitutionPair(PredOf(ctxf, DotTerm), Box(prog, GreaterEqual(DotTerm, Number(0)))) :: Nil)
        AxiomaticRule("CQ equation congruence", s)(
          Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, GreaterEqual(term1, Number(0))),
          Box(prog, GreaterEqual(term2, Number(0)))
          )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
      }
  
  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (manual test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into \\forall x context (schematic test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val context = Forall(Seq(x), DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(x), fml1), Forall(Seq(x), fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }
  
  it should "instantiate CE from x=0 <-> x^2=0 into [x:=5] context (schematic test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "x:=5;".asProgram
    val context = Box(prog, DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, fml1), Box(prog, fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  it should "instantiate CE from x=0 <-> x^2=0 into [x'=5] context (schematic test)" taggedAs USubstTest in {
    val fml1 = "x=0".asFormula
    val fml2 = "x^2=0".asFormula
    val fml = Equiv(fml1, fml2)
    val prog = "x'=5;".asProgram  //ODESystem(Seq(), AtomicODE(Derivative(Real, x), Number(5)), True)
    val context = Box(prog, DotFormula)
    val s = USubst(
      SubstitutionPair(PredOf(pn_, Anything), fml1) ::
      SubstitutionPair(PredOf(qn_, Anything), fml2) ::
      SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
    AxiomaticRule("CE congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Box(prog, fml1), Box(prog, fml2))))
      ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
  }

  
  ignore should "?instantiate CQ from z^2*y=-(-z)^2*-y+0 in complex contexts" taggedAs OptimisticTest in {
    val term1 = "z^2*y".asTerm
    val term2 = "-(-z)^2*-y+0".asTerm
    val fml = Equal(term1, term2)
    val prog = "y:=y-1;{z:=-z+2++z:=0}".asProgram
    val u = Variable("u", None, Real)
    val s = USubst(
      SubstitutionPair(FuncOf(f1_, Anything), term1) ::
      SubstitutionPair(FuncOf(g1_, Anything), term2) ::
      SubstitutionPair(PredOf(ctxf, DotTerm), Forall(Seq(u), Box(prog, GreaterEqual(DotTerm, u)))) :: Nil)
    AxiomaticRule("CQ equation congruence", s)(
      Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(Forall(Seq(u), Box(prog, GreaterEqual(term1, u))),
      Forall(Seq(u), Box(prog, GreaterEqual(term2, u)))
      )))) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
     }
  
   it should "instantiate CQ from z^2*y=-(-z)^2*-y+0 in random contexts" taggedAs USubstTest in {
       val term1 = "z^2*y".asTerm
       val term2 = "-(-z)^2*-y+0".asTerm
       val fml = Equal(term1, term2)
       val context = rand.nextDotFormula(randomComplexity)
       println("Random context " + context.prettyString)
       val s = USubst(
         SubstitutionPair(FuncOf(f1_, Anything), term1) ::
         SubstitutionPair(FuncOf(g1_, Anything), term2) ::
         SubstitutionPair(PredOf(ctxf, DotTerm), context) :: Nil)
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
        SubstitutionPair(PredOf(pn_, Anything), fml1) ::
        SubstitutionPair(PredOf(qn_, Anything), fml2) ::
        SubstitutionPair(PredicationalOf(ctx, DotFormula), context) :: Nil)
      AxiomaticRule("CE congruence", s)(
        Sequent(Seq(), IndexedSeq(), IndexedSeq(Equiv(contextapp(context, fml1), contextapp(context, fml2))))
        ) should be (List(Sequent(Seq(), IndexedSeq(), IndexedSeq(fml))))
 }

 // apply given context to the given argument
  def contextapp(context: Term, arg: Term) : Term =
   USubst(SubstitutionPair(DotTerm, arg) :: Nil)(context)

  def contextapp(context: Formula, arg: Term) : Formula =
    USubst(SubstitutionPair(DotTerm, arg) :: Nil)(context)
  
  def contextapp(context: Formula, arg: Formula) : Formula = {
    val mycontext = Function("dottingC_", None, Bool, Bool)//@TODO eisegesis  should be Function("dottingC_", None, Real->Bool, Bool) //@TODO introduce function types or the Predicational datatype

    USubst(SubstitutionPair(PredicationalOf(mycontext, DotFormula), context) :: Nil)(PredicationalOf(mycontext, arg))
  }
}