package btactics

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.ImplicitDiffAxiom._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

class ImplicitDiffAxiomTests extends TacticTestBase {

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
    //todo: parsing axs(0).conclusion shouldBe "==> (exp<<<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1)>>(g(|t_|)))'=exp<<<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1)>>(g(|t_|))*(g(|t_|))'".asSequent
  }

  it should "derive differential axiom 2" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF

    val axs = deriveDiffAxiom(List(sin,cos))
    println(axs)

    axs.length shouldBe 2
    axs(0) shouldBe 'proved
    axs(1) shouldBe 'proved
    // todo parsing
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

  "property" should "manual proof" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val init = deriveInitCond(exp)
    val diff = ImplicitDiffAxiom.deriveDiffAxiom(List(exp)).head

    // Manually register the differential axiom so that "derive" picks it up automatically
    val info = (diff,PosInExpr(0::Nil),PosInExpr(1::Nil)::Nil)
    AxIndex.implFuncDiffs += (exp -> (info::Nil))
    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (exp -> (init::Nil))

    // exp(y^2) >= 1
    val pr = proveBy(GreaterEqual(FuncOf(exp,Power(Variable("y"),Number(2))),Number(1)),
      propDiffUnfold(Variable("y"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT, //prove from initial conditions
        dC("y >= 0".asFormula)(1) <(
          dI('diffInd)(1) <(id,
            // this is just to test deriving. the proof doesn't work right away, but would work if we separately proved exp(y^2)>=0 as a cut (or diff cut)
            // then the resulting goal is exp(y^2)*2y >= 0
            Dassignb(1) & skip
          ),
          hideL(-2) & ODE(1)
        ),
        skip
      )
    )
    println(pr)

    // todo: parsing
    pr.subgoals.length shouldBe 2
  }

  it should "manual proof with weird subexpression" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val init = deriveInitCond(exp)
    val diff = ImplicitDiffAxiom.deriveDiffAxiom(List(exp)).head

    // Manually register the differential axiom so that "derive" picks it up automatically
    val info = (diff,PosInExpr(0::Nil),PosInExpr(1::Nil)::Nil)
    AxIndex.implFuncDiffs += (exp -> (info::Nil))
    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (exp -> (init::Nil))

    // exp(y+g(x)) > 0
    val pr = proveBy(Greater(FuncOf(exp,"y+g(x)".asTerm),Number(0)),
      propDiffUnfold("y+g(x)".asTerm, Number(0))(1) <(
        SimplifierV3.simplify(1) & QE, //prove from initial conditions
        skip,
        skip
      )
    )
    println(pr)

    // todo: parsing
    pr.subgoals.length shouldBe 2
  }

  it should "multivariate manual proof" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val init = deriveInitCond(exp)
    val diff = ImplicitDiffAxiom.deriveDiffAxiom(List(exp)).head

    // Manually register the differential axiom so that "derive" picks it up automatically
    val info = (diff,PosInExpr(0::Nil),PosInExpr(1::Nil)::Nil)
    AxIndex.implFuncDiffs += (exp -> (info::Nil))
    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (exp -> (init::Nil))

    // exp(x+y) = exp(x)exp(y)
    val pr = proveBy(Equal(FuncOf(exp,"x+y".asTerm),Times(FuncOf(exp,"x".asTerm),FuncOf(exp,"y".asTerm))),
      propDiffUnfold(Variable("x"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT,
        skip, //todo needs dbx to work with function abstraction in QE
        skip
      )
    )
    println(pr)

    // todo: parsing
    pr.subgoals.length shouldBe 2
  }

  it should "multivariate manual proof sin/cos" in withMathematica { _ =>

    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val init1 = deriveInitCond(sin)
    val init2 = deriveInitCond(cos)
    val diff = ImplicitDiffAxiom.deriveDiffAxiom(List(sin,cos))

    // Manually register the differential axiom so that "derive" picks it up automatically
    val info1 = (diff(0),PosInExpr(0::Nil),PosInExpr(1::Nil)::Nil)
    AxIndex.implFuncDiffs += (sin -> (info1::Nil))

    val info2 = (diff(1),PosInExpr(0::Nil),PosInExpr(1::Nil)::Nil)
    AxIndex.implFuncDiffs += (cos -> (info2::Nil))

    // Manually register the initial value axiom so that the simplifier picks it up automatically
    SimplifierV3.implFuncSimps += (sin -> (init1::Nil))
    SimplifierV3.implFuncSimps += (cos -> (init2::Nil))

    // exp(x+y) = exp(x)exp(y)
    val pr = proveBy(Equal(Plus(Power(FuncOf(sin,"z".asTerm),Number(2)),Power(FuncOf(cos,"z".asTerm),Number(2))), Number(1)),
      propDiffUnfold(Variable("z"), Number(0))(1) <(
        SimplifierV3.simplify(1) & closeT,
        dI('diffInd)(1) <(id, Dassignb(1) &
          abbreviateInterpretedFuncs & QE),
        dI('diffInd)(1) <(id, Dassignb(1)  &
          abbreviateInterpretedFuncs & QE)
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
    val diff = ImplicitDiffAxiom.deriveDiffAxiom(List(sin,cos))

    // Manually register the differential axiom so that "derive" picks it up automatically
    val info1 = (diff(0),PosInExpr(0::Nil),PosInExpr(1::Nil)::Nil)
    AxIndex.implFuncDiffs += (sin -> (info1::Nil))

    val info2 = (diff(1),PosInExpr(0::Nil),PosInExpr(1::Nil)::Nil)
    AxIndex.implFuncDiffs += (cos -> (info2::Nil))

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
        skip, //todo: should prove with dgvdbx
        skip
      ))
    println(pr)
  }


}
