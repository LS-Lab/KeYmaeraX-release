package btactics

import edu.cmu.cs.ls.keymaerax.btactics.ImplicitAx._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, InterpretedSymbols}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

class ImplicitAxTests extends TacticTestBase {

  "definitions" should "derive defining axiom" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val ax = getDefAx(exp)

    ax.isDefined shouldBe true
    ax.get.provable.conclusion shouldBe "==> ._0=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>(._1)<-><{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)".asSequent
  }

  it should "derive defining axiom 2" in withMathematica { _ =>
    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val ax1 = getDefAx(sin)
    val ax2 = getDefAx(cos)

    ax1.isDefined shouldBe true
    ax2.isDefined shouldBe true
    ax1.get.provable.conclusion shouldBe "==>  ._0=sin<< <{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0) >>(._1)<-><{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)".asSequent
    ax2.get.provable.conclusion shouldBe "==>  ._0=cos<< <{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0) >>(._1)<-><{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)".asSequent
  }

  it should "derive defining axiom 3" in withMathematica { _ =>
    // Tanh with a different t_ variable and weird starting time
    val tanh = Function("tanh",None,Real,Real,Some("<{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=100)".asFormula))

    val ax = getDefAx(tanh)

    ax.isDefined shouldBe true
    ax.get.provable.conclusion shouldBe "==>  ._0=tanh<< <{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=100) >>(._1)<-><{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=100)".asSequent
  }


  it should "derive defining axiom 4" in withMathematica { _ =>
    // note: this already requires the rest of the proofs to work
    val exp = Function("ee",None,Real,Real,Some("<{ee:=._0;t_:=._1;}{{ee'=-exp(t_)*ee,t_'=-(1)}++{ee'=exp(t_)*ee,t_'=1}}>(ee=1&t_=0)".asFormula))

    val ax = getDefAx(exp)

    ax.isDefined shouldBe true
    println(ax.get.provable.conclusion)
  }

  it should "derive defining axiom 5" in withMathematica { _ =>
    // note: this already requires the rest of the proofs to work
    val exp = Function("eee",None,Real,Real,Some("<{eee:=._0;t_:=._1;}{{eee'=-eee*exp(t_^2),t_'=-(1)}++{eee'=eee*exp(t_^2),t_'=1}}>(eee=sin(1+cos(2))&t_=sin(0))".asFormula))
    val exp2 = Function("eee",None,Real,Real,Some("<{eee:=._0;t_:=._1;}{{eee'=-eee*exp(t_),t_'=-(1)}++{eee'=eee*exp(t_),t_'=1}}>(eee=sin(1+cos(2))&t_=sin(0))".asFormula))

    val ax = getDefAx(exp) //defeee.alp

    ax.isDefined shouldBe true
    println(ax.get.provable.conclusion)
  }

  "compose" should "lift partial to diff axiom" in withMathematica { _ =>

    val ax = DcomposeFull
    println(ax)
    ax.fact shouldBe 'proved
  }

  it should "prove flip axiom" in withMathematica { _ =>

    val ax = flipPartial
    println(ax)
    ax.fact shouldBe 'proved
  }

  "reverse" should "prove there and back style axiom" in withMathematica { _ =>

    val pr = thereAndBack(2)

    println(pr)

    pr shouldBe 'proved
    pr.conclusion shouldBe "==> p_(x__1,x__2)->[{x__1'=f__1(x__1,x__2),x__2'=f__2(x__1,x__2)&q_(x__1,x__2)}]<{x__1'=-f__1(x__1,x__2),x__2'=-f__2(x__1,x__2)&q_(x__1,x__2)}>p_(x__1,x__2)".asSequent
  }

  it should "prove definition box expansion" in withMathematica { _ =>

    val pr = defExpandToBox("e'=e".asDifferentialProgram)

    println(pr)
    pr shouldBe 'proved
    pr.conclusion shouldBe "==>  <{e'=-e&q_(e)}>p_(e)|<{e'=e&q_(e)}>p_(e)->[{e'=e&q_(e)}]<{e'=-e&q_(e)}>p_(e)|[{e'=-e&q_(e)}]<{e'=e&q_(e)}>p_(e)".asSequent
  }

  it should "prove sin/cos box expansion" in withMathematica { _ =>

    val pr = defExpandToBox("s'=c,c'=-s".asDifferentialProgram)

    println(pr)
    pr shouldBe 'proved
    pr.conclusion shouldBe "==>  <{s'=-c,c'=--s&q_(s,c)}>p_(s,c)|<{s'=c,c'=-s&q_(s,c)}>p_(s,c)->[{s'=c,c'=-s&q_(s,c)}]<{s'=-c,c'=--s&q_(s,c)}>p_(s,c)|[{s'=-c,c'=--s&q_(s,c)}]<{s'=c,c'=-s&q_(s,c)}>p_(s,c)".asSequent
  }

  "first deriv" should "prove first derivative axiom" in withMathematica { _ =>

    val ax = firstDer
    println(ax)
    ax.fact shouldBe 'proved
  }

  it should "prove forward partial derivatives" in withMathematica { _ =>
    val pr = partialDer(2)

    println(pr)

    pr shouldBe 'proved
    pr.conclusion shouldBe "==>  [{x__1'=f__1(x__1,x__2,t_),x__2'=f__2(x__1,x__2,t_),t_'=h_()}](x__1=g__1(t_)&x__2=g__2(t_))->[t_':=h_();]((g__1(t_))'=f__1(g__1(t_),g__2(t_),t_)&(g__2(t_))'=f__2(g__1(t_),g__2(t_),t_))".asSequent
  }

  "derive diff ax" should "derive differential axiom" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

    axs.length shouldBe 1
    axs(0) shouldBe 'proved
    axs(0).conclusion shouldBe "==>  (exp<<<{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>(g(|TDIFFAX_|)))'=exp<<<{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>(g(|TDIFFAX_|))*(g(|TDIFFAX_|))'".asSequent
  }

  it should "derive differential axiom 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF

    val axs = deriveDiffAxiom(List(sin,cos))
    println(axs)

    axs.length shouldBe 2
    axs(0) shouldBe 'proved
    axs(1) shouldBe 'proved
    axs(0).conclusion shouldBe "==>  (sin<<<{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))'=cos<<<{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|))*(g(|TDIFFAX_|))'".asSequent
    axs(1).conclusion shouldBe "==>  (cos<<<{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))'=(-sin<<<{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))*(g(|TDIFFAX_|))'".asSequent
  }

  it should "derive differential axiom with time" in withMathematica { _ =>

    val exp = Function(name="expt",domain=Real, sort=Real,
      interp = Some(/* ._0 = exp(._1) <-> */ "<{e:=._0; t :=._1;} {{e'=-(t),t'=-(1)} ++ {e'=t,t'=1}}> (e=1 & t=0)".asFormula))

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

    axs.length shouldBe 1
    axs(0) shouldBe 'proved
    axs(0).conclusion shouldBe "==>  (expt<< <{e:=._0;t:=._1;}{{e'=-t,t'=-(1)}++{e'=t,t'=1}}>(e=1&t=0) >>(g(|TDIFFAX_|)))'=g(|TDIFFAX_|)*(g(|TDIFFAX_|))'".asSequent

  }

  it should "derive differential axiom with weird init" in withMathematica { _ =>

    val exp = Function(name="exptt",domain=Real, sort=Real,
      interp = Some(/* ._0 = exp(._1) <-> */ "<{e:=._0; t :=._1;} {{e'=-(t),t'=-(1)} ++ {e'=t,t'=1}}> (e=1 & t=10)".asFormula))

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

    axs.length shouldBe 1
    axs(0) shouldBe 'proved
    axs(0).conclusion shouldBe "==>  (exptt<< <{e:=._0;t:=._1;}{{e'=-t,t'=-(1)}++{e'=t,t'=1}}>(e=1&t=10) >>(g(|TDIFFAX_|)))'=g(|TDIFFAX_|)*(g(|TDIFFAX_|))'".asSequent

  }

  it should "derive dependent differential axiom" in withMathematica { _ =>

    val exp = Function(name="expA",domain=Real, sort=Real,
      interp = Some(/* ._0 = exp(._1) <-> */ "<{e:=._0; t :=._1;} {{e'=-(exp(t)*e),t'=-(1)} ++ {e'=exp(t)*e,t'=1}}> (e=1 & t=10)".asFormula))

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

    axs.length shouldBe 1
    axs(0) shouldBe 'proved
    axs(0).conclusion shouldBe "==>  (expA<< <{e:=._0;t:=._1;}{{e'=-exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(t)*e,t'=-(1)}++{e'=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(t)*e,t'=1}}>(e=1&t=10) >>(g(|TDIFFAX_|)))'=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(g(|TDIFFAX_|))*expA<< <{e:=._0;t:=._1;}{{e'=-exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(t)*e,t'=-(1)}++{e'=exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(t)*e,t'=1}}>(e=1&t=10) >>(g(|TDIFFAX_|))*(g(|TDIFFAX_|))'".asSequent

  }

  it should "derive differential axiom nested" in withMathematica { _ =>

    val exp = Function(name="expB",domain=Real, sort=Real,
      interp = Some( "<{expB:=._0;t:=._1;}{{expB'=-exp(t)*expB,t'=-(1)}++{expB'=exp(t)*expB,t'=1}}>(expB=100&t=0) ".asFormula))
    //interp = Some( "<{expB:=._0;t:=._1;}{{expB'=-expA<< <{expA:=._0;t:=._1;}{{expA'=-expA,t'=-(1)}++{expA'=expA,t'=1}}>(expA=1&t=0) >>(t)*expB,t'=-(1)}++{expB'=expA<< <{expA:=._0;t:=._1;}{{expA'=-expA,t'=-(1)}++{expA'=expA,t'=1}}>(expA=1&t=0) >>(t)*expB,t'=1}}>(expB=expA<< <{expA:=._0;t:=._1;}{{expA'=-expA,t'=-(1)}++{expA'=expA,t'=1}}>(expA=1&t=0) >>(1)&t=0) ".asFormula))

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

//    axs.length shouldBe 1
//    axs(0) shouldBe 'proved
//    axs(0).conclusion shouldBe "==>  (exp<< <{e:=._0;t:=._1;}{{e'=-t,t'=-(1)}++{e'=t,t'=1}}>(e=1&t=10) >>(g(|TDIFFAX_|)))'=g(|TDIFFAX_|)*(g(|TDIFFAX_|))'".asSequent

  }

  it should "derive differential axiom from single" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val axs = deriveDiffAxiomSing(sin)

    println(axs)

    axs.length shouldBe 2
    axs(0)._1 shouldBe sin
    axs(1)._1 shouldBe cos
    axs(0)._2 shouldBe 'proved
    axs(1)._2 shouldBe 'proved
    axs(0)._2.conclusion shouldBe "==>  (sin<<<{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))'=cos<<<{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|))*(g(|TDIFFAX_|))'".asSequent
    axs(1)._2.conclusion shouldBe "==>  (cos<<<{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))'=(-sin<<<{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))*(g(|TDIFFAX_|))'".asSequent
  }

  it should "derive differential axiom from single reorder" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val axs = deriveDiffAxiomSing(cos)

    println(axs)

    axs.length shouldBe 2
    axs(0)._1 shouldBe sin
    axs(1)._1 shouldBe cos
    axs(0)._2 shouldBe 'proved
    axs(1)._2 shouldBe 'proved
    axs(0)._2.conclusion shouldBe "==>  (sin<<<{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))'=cos<<<{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|))*(g(|TDIFFAX_|))'".asSequent
    axs(1)._2.conclusion shouldBe "==>  (cos<<<{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))'=(-sin<<<{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0)>>(g(|TDIFFAX_|)))*(g(|TDIFFAX_|))'".asSequent
  }

  "init" should "derive initial condition" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val ax = deriveInitAxiom(exp)
    println(ax)

    ax shouldBe 'proved
  }

  "derivedaxiominfo" should "derive and store diff ax 1" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val dexp = getDiffAx(exp)

    dexp.isDefined shouldBe true
    dexp.get.provable.conclusion shouldBe "==>  (exp<<<{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>(g(|TDIFFAX_|)))'=exp<<<{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0)>>(g(|TDIFFAX_|))*(g(|TDIFFAX_|))'".asSequent
  }

  it should "derive and store diff ax 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val dsin = getDiffAx(sin)
    val dcos = getDiffAx(cos)

    dsin.isDefined shouldBe true
    dsin.get.provable shouldBe 'proved
    dcos.isDefined shouldBe true
    dcos.get.provable shouldBe 'proved
  }

  it should "diff ax fail gracefully" in withMathematica { _ =>

    val fake = Function("fake",None, Real, Real,interp = Some(True))
    println(fake)

    getDiffAx(fake) shouldBe None
  }
  it should "derive and store init ax 1" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val dexp = getInitAx(exp)

    println(dexp)
    dexp.isDefined shouldBe true
    dexp.get.provable.conclusion shouldBe "==> exp<< <{exp:=._0;t:=._1;}{{exp'=-exp,t'=-(1)}++{exp'=exp,t'=1}}>(exp=1&t=0) >>(0)=1".asSequent
  }

  it should "derive and store init ax 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val dsin = getInitAx(sin)
    val dcos = getInitAx(cos)

    println(dsin)
    println(dcos)
    dsin.isDefined shouldBe true
    dsin.get.provable shouldBe 'proved
    dcos.isDefined shouldBe true
    dcos.get.provable shouldBe 'proved
  }

  it should "init ax fail gracefully" in withMathematica { _ =>

    val fake = Function("fake",None, Real, Real,interp = Some(True))
    println(fake)

    getInitAx(fake) shouldBe None
  }

  it should "detect multiple definitions with same function name 1" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val exp2 = Function("exp",None,Real,Real,Some("<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(exp=2&t_=0)".asFormula))
    val dexp = getDiffAx(exp)

    the [Exception] thrownBy getDiffAx(exp2) should have message "Duplicate function names with different interpretations used in same session."
  }

  it should "detect multiple definitions with same function name 2" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val exp2 = Function("exp",None,Real,Real,Some("<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(exp=2&t_=0)".asFormula))
    val dexp = getInitAx(exp)

    the [Exception] thrownBy getInitAx(exp2) should have message "Duplicate function names with different interpretations used in same session."
  }

  it should "detect multiple definitions with same function name 3" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val exp2 = Function("exp",None,Real,Real,Some("<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(exp=2&t_=0)".asFormula))
    val dexp = getDefAx(exp)

    the [Exception] thrownBy getDefAx(exp2) should have message "Duplicate function names with different interpretations used in same session."
  }

  "diff unfold" should "diff unfold both directions" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    val pr = proveBy(Greater(FuncOf(exp,"f()".asTerm),Number(0)),
      diffUnfold("f()".asTerm, "g()".asTerm)(1)
    )

    println(pr)
    pr.subgoals.length shouldBe 3
    pr.subgoals(0) shouldBe "==>  exp(g())>0".asSequent
    pr.subgoals(1) shouldBe "v=g(), exp(v)>0  ==>  [{v'=1 & v <= f()}]exp(v)>0".asSequent
    pr.subgoals(2) shouldBe "v=g(), exp(v)>0  ==>  [{v'=(-1) & f() <= v}]exp(v)>0".asSequent
  }

  it should "prove exp non-negative" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    val pr = proveBy(Greater(FuncOf(exp,"f()".asTerm),Number(0)),
      diffUnfold("f()".asTerm, Number(0))(1) <(
        QE,
        dbx(Some(Number(1)))(1),
        dbx(Some(Number(-1)))(1)
      ))

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove exp > 1" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    val pr = proveBy(GreaterEqual(FuncOf(exp,"x^2".asTerm),Number(1)),
      diffUnfold("x^2".asTerm, Number(0))(1) <(
        QE,
        ODE(1),
        dC("v=0".asFormula)(1) <(
          ODE(1),
          ODE(1)
        )
      ))

    println(pr)
    pr shouldBe 'proved
  }

  it should "manual proof with weird subexpression" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    // exp(y+g(x)) > 0
    val pr = proveBy(Greater(FuncOf(exp,"y+g(x)".asTerm),Number(0)),
      diffUnfold("y+g(x)".asTerm, Number(0))(1) <(
        QE, //prove from initial conditions
        dbx(Some(Number(1)))(1),
        dbx(Some(Number(-1)))(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "multivariate auto proof" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    // exp(x+y) = exp(x)exp(y)
    val pr = proveBy(Equal(FuncOf(exp,"x+y".asTerm),Times(FuncOf(exp,"x".asTerm),FuncOf(exp,"y".asTerm))),
      diffUnfold(Variable("x"), Number(0))(1) <(
        QE,
        dbx(None)(1),
        dbx(None)(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "multivariate manual proof sin/cos" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF

    val pr = proveBy(Equal(Plus(Power(FuncOf(sin,"z".asTerm),Number(2)),Power(FuncOf(cos,"z".asTerm),Number(2))), Number(1)),
      diffUnfold(Variable("z"), Number(0))(1) <(
        QE,
        dI('full)(1),
        dI('diffInd)(1) <(id, Dassignb(1) & QE)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "multivariate manual proof sin/cos 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val init1 = deriveInitAxiom(sin)
    val init2 = deriveInitAxiom(cos)

    val x = Variable("x")
    val y = Variable("y")
    val v = Variable("v")
    val sinx=FuncOf(sin,x)
    val siny=FuncOf(sin,y)
    val cosx=FuncOf(cos,x)
    val cosy=FuncOf(cos,y)
    val sinv=FuncOf(sin,v)
    val cosv=FuncOf(cos,v)

    val p1 =
      Minus(FuncOf(sin,Plus(v,y)),Plus(Times(sinv,cosy),Times(cosv,siny)))
    val p2 =
      Minus(FuncOf(cos,Plus(v,y)), Minus(Times(cosv,cosy),Times(sinv,siny)))

    val G = List(List(Number(0),Number(1)),List(Number(-1),Number(0)))
    val Gn = List(List(Number(0),Number(-1)),List(Number(1),Number(0)))

    // sin(x+y) = sin(x)cos(y)+cos(x)sin(y)
    // cos(x+y) = cos(x)cos(y)-sin(x)sin(y)
    val pr = proveBy(
      And(
        Equal(
          FuncOf(sin,Plus(x,y)),
          Plus(Times(sinx,cosy),Times(cosx,siny))
        ),
        Equal(
          FuncOf(cos,Plus(x,y)),
          Minus(Times(cosx,cosy),Times(sinx,siny))
        )
      ),
      diffUnfold(Variable("x"), Number(0))(1) <(
        QE,
        ODEInvariance.dgVdbx(G,p1::p2::Nil)(1) & DW(1) & TactixLibrary.G(1) & QE,
        ODEInvariance.dgVdbx(Gn,p1::p2::Nil)(1) & DW(1) & TactixLibrary.G(1) & QE
      ))
    println(pr)
    pr shouldBe 'proved
  }

  it should "multivariate manual proof sin/cos auto" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val init1 = deriveInitAxiom(sin)
    val init2 = deriveInitAxiom(cos)
    val x = Variable("x")
    val y = Variable("y")
    val sinx=FuncOf(sin,x)
    val siny=FuncOf(sin,y)
    val cosx=FuncOf(cos,x)
    val cosy=FuncOf(cos,y)

    // sin(x+y) = sin(x)cos(y)+cos(x)sin(y)
    // cos(x+y) = cos(x)cos(y)-sin(x)sin(y) automatically generated
    val pr = proveBy(
        Equal(
          FuncOf(sin,Plus(x,y)),
          Plus(Times(sinx,cosy),Times(cosx,siny))
        ),
      diffUnfold(Variable("x"), Number(0))(1) <(
        QE,
        ODEInvariance.dRI(1),
        ODEInvariance.dRI(1)
      ))
    println(pr)

    pr shouldBe 'proved
  }

  it should "multivariate manual proof sin/cos auto 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val x = Variable("x")
    val sinx=FuncOf(sin,x)
    val cosx=FuncOf(cos,x)

    // sin(2*x) = 2*sin(x)*cos(x)
    val pr = proveBy(
      Equal(
        FuncOf(sin,Times(Number(2),x)),
        Times(Number(2),Times(sinx,cosx))
      ),
      diffUnfold(Variable("x"), Number(0))(1) <(
        QE,
        ODEInvariance.dRI(1),
        ODEInvariance.dRI(1)
      ))
    println(pr)
    pr shouldBe 'proved
  }

  it should "prove example with no semialgebraic invariant" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    val diffcut = LessEqual("x".asVariable, FuncOf(exp,"t^2-t".asTerm))

    val pr = proveBy("t=0&x<=1 -> [{x'=x*(2*t-1),t'=1}](t=1->x<=1)".asFormula,
      implyR(1) & andL(-1) &
      dC(diffcut)(1) <(
        DW(1) & G(1) & QE,
        dbx(None)(1)
      )
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "expand abbreviations of interpreted symbols in ODE" in withMathematica { _ =>
    val entry = ArchiveParser(
      """ArchiveEntry "exp"
        |Definitions implicit Real e(Real t) '= {{e:=1;t:=2;}; {e'=-e,t'=1}}; End.
        |ProgramVariables Real x; End.
        |Problem e(x) > 0 End.
        |End.
        |""".stripMargin).head
    proveBy(entry.sequent, ImplicitAx.diffUnfold(Variable("x"), Number(2))(1) <(
      QE,
      ODE(1),
      ODE(1)
    ), entry.defs) shouldBe 'proved
  }

  it should "diff unfold D existentials" in withMathematica { _ =>
    
    val pr = proveBy("k > 0 -> \\exists x ( x >= l & exp(-x) < k )".asFormula,
      implyR(1) &
      diffUnfoldD("l".asTerm)(1) & orR(1) & hideR(2) &
      ODELiveness.kDomainDiamond("exp(-v) < k".asFormula)(1) <(
        ODELiveness.dV("k".asTerm)(1),
        ODE(1)
      )
    )

    println(pr)
    pr shouldBe 'proved
  }

  it should "prove pi with RCF" in withMathematica { _ =>

    val pr = proveBy("cos(pi()/2) = 0".asFormula,
      RCF
    )
    println(pr)

    pr shouldBe 'proved
  }

  it should "work correctly with composition" in withMathematica { _=>

    val pr = proveBy("v=0 -> [{v'=1&v<=x()}]arctan<< <{arctan:=._0;t:=._1;}{{arctan'=-(1/(1+t^2)),t'=-(1)}++{arctan'=1/(1+t^2),t'=1}}>(arctan=0&t=0) >>(sin<< <{cos:=*;sin:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0) >>(v)/cos<< <{sin:=*;cos:=._0;t:=._1;}{{sin'=-cos,cos'=--sin,t'=-(1)}++{sin'=cos,cos'=-sin,t'=1}}>(sin=0&cos=1&t=0) >>(v))=v".asFormula,
      implyR(1) & ODEInvariance.dRI(1)
    )
    println(pr)

    pr shouldBe 'proved
  }

  it should "work with composition correctly 2" in withMathematica { _ =>
    val pr = proveBy("v=0, exp2<< <{exp2:=._0;t:=._1;}{{exp2'=-exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(t)*exp2,t'=-(1)}++{exp2'=exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(t)*exp2,t'=1}}>(exp2=exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(1)&t=0) >>(v)=exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(v))\n  ==>  [{v'=1&v<=x()}]exp2<< <{exp2:=._0;t:=._1;}{{exp2'=-exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(t)*exp2,t'=-(1)}++{exp2'=exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(t)*exp2,t'=1}}>(exp2=exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(1)&t=0) >>(v)=exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(exp1<< <{exp1:=._0;t:=._1;}{{exp1'=-exp1,t'=-(1)}++{exp1'=exp1,t'=1}}>(exp1=1&t=0) >>(v))".asSequent,
      ODEInvariance.dRI(1)
    )

    println(pr)
    pr shouldBe 'proved
  }
}
