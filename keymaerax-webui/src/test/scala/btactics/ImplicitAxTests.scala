package btactics

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.ImplicitAx._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import DerivationInfoAugmentors._

class ImplicitAxTests extends TacticTestBase {

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
    axs(0).conclusion shouldBe "==>  (exp<<<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1)>>(g(|t_|)))'=exp<<<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1)>>(g(|t_|))*(g(|t_|))'".asSequent
  }

  it should "derive differential axiom 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF

    val axs = deriveDiffAxiom(List(sin,cos))
    println(axs)

    axs.length shouldBe 2
    axs(0) shouldBe 'proved
    axs(1) shouldBe 'proved
    axs(0).conclusion shouldBe "==>  (sin<<<{cos:=*;sin:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|)))'=cos<<<{sin:=*;cos:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|))*(g(|t_|))'".asSequent
    axs(1).conclusion shouldBe "==>  (cos<<<{sin:=*;cos:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|)))'=(-sin<<<{cos:=*;sin:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|)))*(g(|t_|))'".asSequent
  }

  it should "derive differential axiom 3" in withMathematica { _ =>

    val f1 = Function(name="f1",domain=Real, sort=Real,
      interp = Some("<{b:= *; c:=*; a:=._0; t :=._1;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (t=0&a=0&b=0&c=0)".asFormula))
    val f2 = Function(name="f2",domain=Real, sort=Real,
      interp = Some("<{a:= *; c:=*; b:=._0; t :=._1;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (t=0&a=0&b=0&c=0)".asFormula))
    val f3 = Function(name="f3",domain=Real, sort=Real,
      interp = Some("<{b:=*; a:=*; c:=._0; t :=._1;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (t=0&a=0&b=0&c=0)".asFormula))

    val axs = deriveDiffAxiom(List(f1,f2,f3))
    println(axs)

    axs.length shouldBe 3
    axs(0) shouldBe 'proved
    axs(1) shouldBe 'proved
    axs(2) shouldBe 'proved

    axs(0).conclusion shouldBe "==>  (f1<<<{b:=*;c:=*;a:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|)))'=(f2<<<{a:=*;c:=*;b:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))+5)*(g(|t_|))'".asSequent
    axs(1).conclusion shouldBe "==>  (f2<<<{a:=*;c:=*;b:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|)))'=f3<<<{b:=*;a:=*;c:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))*f1<<<{b:=*;c:=*;a:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))*(g(|t_|))'".asSequent
    axs(2).conclusion shouldBe "==>  (f3<<<{b:=*;a:=*;c:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|)))'=f1<<<{b:=*;c:=*;a:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))^2*(g(|t_|))'".asSequent
  }

  it should "derive differential axiom with time" in withMathematica { _ =>

    val exp = Function(name="exp",domain=Real, sort=Real,
      interp = Some(/* ._0 = exp(._1) <-> */ "<{e:=._0; t :=._1;} {{e'=-(t),t'=-(1)} ++ {e'=t,t'=1}}> (t=0 & e=1)".asFormula))

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

    axs.length shouldBe 1
    axs(0) shouldBe 'proved
  }

  "init" should "derive initial condition" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val ax = deriveInitCond(exp)
    println(ax)

    ax shouldBe 'proved
  }

  it should "derive initial condition 3" in withMathematica { _ =>

    val f1 = Function(name="f1",domain=Real, sort=Real,
      interp = Some("<{b:= *; c:=*; a:=._0; t :=._1;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (t=2&a=0&b=0&c=0)".asFormula))
    val f2 = Function(name="f2",domain=Real, sort=Real,
      interp = Some("<{a:= *; c:=*; b:=._0; t :=._1;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (t=2&a=0&b=0&c=0)".asFormula))
    val f3 = Function(name="f3",domain=Real, sort=Real,
      interp = Some("<{b:=*; a:=*; c:=._0; t :=._1;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (t=2&a=0&b=0&c=0)".asFormula))

    val ax1 = deriveInitCond(f1)
    val ax2 = deriveInitCond(f2)
    val ax3 = deriveInitCond(f3)

    // Note: the implementation works at an initial time other than t=0
    println(ax1)
    println(ax2)
    println(ax3)

    ax1 shouldBe 'proved
    ax2 shouldBe 'proved
    ax3 shouldBe 'proved
  }

  "derivedaxiominfo" should "derive and store diff ax 1" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val diff = deriveDiffAxiomReg(List(exp)).head

    getDiffAx(exp).isDefined shouldBe true
    getDiffAx(exp).get.provable shouldBe diff
  }

  it should "derive and store diff ax 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val diff = ImplicitAx.deriveDiffAxiom(List(sin,cos))
    val dsin = diff(0)
    val dcos = diff(1)

    registerDiffAx(sin,dsin)
    registerDiffAx(cos,dcos)

    getDiffAx(sin).isDefined shouldBe true
    getDiffAx(sin).get.provable shouldBe dsin
    getDiffAx(cos).isDefined shouldBe true
    getDiffAx(cos).get.provable shouldBe dcos
  }

  "property" should "prove exp non-negative" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val init = deriveInitCond(exp)
    deriveDiffAxiomReg(List(exp))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (exp -> (init::Nil))

    val pr = proveBy(Greater(FuncOf(exp,"f()".asTerm),Number(0)),
      propDiffUnfold("f()".asTerm, Number(0))(1) <(
        SimplifierV3.simplify(1) & QE,
        dbx(Some(Number(1)))(1),
        dbx(Some(Number(-1)))(1)
      ))

    println(pr)
    pr shouldBe 'proved
  }

  it should "manual proof" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val init = deriveInitCond(exp)
    deriveDiffAxiomReg(List(exp))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (exp -> (init::Nil))

    // exp(y^2) >= 1
    val pr = proveBy(GreaterEqual(FuncOf(exp,Power(Variable("y"),Number(2))),Number(1)),
      propDiffUnfold(Variable("y"), Number(0))(1) <(
        SimplifierV3.simplify(1) & QE, //prove from initial conditions
        dC("y >= 0".asFormula)(1) <(
          dI('diffInd)(1) <(id,
            // this is just to test deriving. the proof doesn't work right away, but would work if we separately proved exp(y^2)>=0 as a cut (or diff cut)
            // then the resulting goal is exp(y^2)*2y >= 0
            Dassignb(1) & cohideR(1)
          ),
          hideL(-2) & ODE(1)
        ),
        skip
      )
    )
    println(pr)
    pr.subgoals.length shouldBe 2
    pr.subgoals(0) shouldBe "==>  exp<< <{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1) >>(y^2)*(2*y^(2-1)*1)>=0".asSequent
    pr.subgoals(1) shouldBe "y=0, exp<< <{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1) >>(y^2)>=1  ==>  [{y'=(-1)}]exp<<<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1)>>(y^2)>=1".asSequent
  }

  it should "manual proof with weird subexpression" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val init = deriveInitCond(exp)
    deriveDiffAxiomReg(List(exp))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (exp -> (init::Nil))

    // exp(y+g(x)) > 0
    val pr = proveBy(Greater(FuncOf(exp,"y+g(x)".asTerm),Number(0)),
      propDiffUnfold("y+g(x)".asTerm, Number(0))(1) <(
        SimplifierV3.simplify(1) & QE, //prove from initial conditions
        dbx(Some(Number(1)))(1),
        dbx(Some(Number(-1)))(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "multivariate manual proof" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val init = deriveInitCond(exp)
    deriveDiffAxiomReg(List(exp))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (exp -> (init::Nil))

    // exp(x+y) = exp(x)exp(y)
    val pr = proveBy(Equal(FuncOf(exp,"x+y".asTerm),Times(FuncOf(exp,"x".asTerm),FuncOf(exp,"y".asTerm))),
      propDiffUnfold(Variable("x"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT,
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
    val init1 = deriveInitCond(sin)
    val init2 = deriveInitCond(cos)
    deriveDiffAxiomReg(List(sin,cos))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (sin -> (init1::Nil))
    SimplifierV3.implFuncSimps += (cos -> (init2::Nil))

    val pr = proveBy(Equal(Plus(Power(FuncOf(sin,"z".asTerm),Number(2)),Power(FuncOf(cos,"z".asTerm),Number(2))), Number(1)),
      propDiffUnfold(Variable("z"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT,
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
    val init1 = deriveInitCond(sin)
    val init2 = deriveInitCond(cos)
    deriveDiffAxiomReg(List(sin,cos))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (sin -> (init1::Nil))
    SimplifierV3.implFuncSimps += (cos -> (init2::Nil))

    val x = Variable("x")
    val y = Variable("y")
    val sinx=FuncOf(sin,x)
    val siny=FuncOf(sin,y)
    val cosx=FuncOf(cos,x)
    val cosy=FuncOf(cos,y)

    val p1 =
      Minus(FuncOf(sin,Plus(x,y)),Plus(Times(sinx,cosy),Times(cosx,siny)))
    val p2 =
      Minus(FuncOf(cos,Plus(x,y)), Minus(Times(cosx,cosy),Times(sinx,siny)))

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
      propDiffUnfold(Variable("x"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT,
        ODEInvariance.dgVdbx(G,p1::p2::Nil)(1) & DW(1) & TactixLibrary.G(1) & QE,
        ODEInvariance.dgVdbx(Gn,p1::p2::Nil)(1) & DW(1) & TactixLibrary.G(1) & QE
      ))
    println(pr)

    pr shouldBe 'proved
  }

  it should "multivariate manual proof sin/cos auto" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val init1 = deriveInitCond(sin)
    val init2 = deriveInitCond(cos)
    deriveDiffAxiomReg(List(sin,cos))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (sin -> (init1::Nil))
    SimplifierV3.implFuncSimps += (cos -> (init2::Nil))

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
      propDiffUnfold(Variable("x"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT,
        ODEInvariance.dRI(1),
        ODEInvariance.dRI(1)
      ))
    println(pr)

    pr shouldBe 'proved
  }

  it should "multivariate manual proof sin/cos auto 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val init1 = deriveInitCond(sin)
    val init2 = deriveInitCond(cos)
    deriveDiffAxiomReg(List(sin,cos))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (sin -> (init1::Nil))
    SimplifierV3.implFuncSimps += (cos -> (init2::Nil))

    val x = Variable("x")
    val sinx=FuncOf(sin,x)
    val cosx=FuncOf(cos,x)

    // sin(2*x) = 2*sin(x)*cos(x)
    val pr = proveBy(
      Equal(
        FuncOf(sin,Times(Number(2),x)),
        Times(Number(2),Times(sinx,cosx))
      ),
      propDiffUnfold(Variable("x"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT,
        ODEInvariance.dRI(1),
        ODEInvariance.dRI(1)
      ))
    println(pr)

    pr shouldBe 'proved
  }

}
