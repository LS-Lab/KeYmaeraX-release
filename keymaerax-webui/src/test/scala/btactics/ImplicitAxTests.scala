package btactics

import edu.cmu.cs.ls.keymaerax.btactics.ImplicitAx._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{InterpretedSymbols, KeYmaeraXArchiveParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

class ImplicitAxTests extends TacticTestBase {

  "definitions" should "derive defining axiom" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val ax = deriveDef(exp)
    ax shouldBe 'proved
    ax.conclusion shouldBe "==> ._0=exp<< <{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(exp=1&t_=0) >>(._1)<-><{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(exp=1&t_=0)".asSequent
  }

  it should "derive defining axiom 2" in withMathematica { _ =>
    val sin = InterpretedSymbols.sinF
    val cos = InterpretedSymbols.cosF
    val ax1 = deriveDef(sin)
    val ax2 = deriveDef(cos)
    ax1 shouldBe 'proved
    ax2 shouldBe 'proved
    println(ax1)
    println(ax2)
    ax1.conclusion shouldBe "==>  ._0=sin<< <{cos:=*;sin:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(sin=0&cos=1&t_=0) >>(._1)<-><{cos:=*;sin:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(sin=0&cos=1&t_=0)".asSequent
    ax2.conclusion shouldBe "==>  ._0=cos<< <{sin:=*;cos:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(sin=0&cos=1&t_=0) >>(._1)<-><{sin:=*;cos:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(sin=0&cos=1&t_=0)".asSequent
  }

  it should "derive defining axiom 3" in withMathematica { _ =>
    val tanh = Function("tanh",None,Real,Real,Some("<{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=0)".asFormula))

    val ax = deriveDef(tanh)
    ax shouldBe 'proved
    println(ax)
    ax.conclusion shouldBe "==>  ._0=tanh<< <{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=0) >>(._1)<-><{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=0)".asSequent
  }

//  it should "derive defining axiom 4" in withMathematica { _ =>
//    // note: this already requires the rest of the proofs to work
//    val exp = Function("ee",None,Real,Real,Some("<{ee:=._0;t_:=._1;}{{ee'=-exp(t_)*ee,t_'=-(1)}++{ee'=exp(t_)*ee,t_'=1}}>(ee=1&t_=0)".asFormula))
//
//    val ax = deriveDef(exp)
//    ax shouldBe 'proved
//    println(ax)
//    ax.conclusion shouldBe "==>  ._0=tanh<< <{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=0) >>(._1)<-><{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(tanh=0&t_=0)".asSequent
//  }

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

    axs(0).conclusion shouldBe "==>  (f1<< <{b:=*;c:=*;a:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|)))'=(f2<<<{a:=*;c:=*;b:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))+5)*(g(|t_|))'".asSequent
    axs(1).conclusion shouldBe "==>  (f2<< <{a:=*;c:=*;b:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|)))'=f3<<<{b:=*;a:=*;c:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))*f1<<<{b:=*;c:=*;a:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))*(g(|t_|))'".asSequent
    axs(2).conclusion shouldBe "==>  (f3<< <{b:=*;a:=*;c:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|)))'=f1<<<{b:=*;c:=*;a:=._0;t:=._1;}{{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)}++{a'=b+5,b'=c*a,c'=a^2,t'=1}}>(t=0&a=0&b=0&c=0)>>(g(|t_|))^2*(g(|t_|))'".asSequent
  }

  it should "derive differential axiom with time" in withMathematica { _ =>

    val exp = Function(name="exp",domain=Real, sort=Real,
      interp = Some(/* ._0 = exp(._1) <-> */ "<{e:=._0; t :=._1;} {{e'=-(t),t'=-(1)} ++ {e'=t,t'=1}}> (t=0 & e=1)".asFormula))

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

    axs.length shouldBe 1
    axs(0) shouldBe 'proved
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
    axs(0)._2.conclusion shouldBe "==>  (sin<<<{cos:=*;sin:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|)))'=cos<<<{sin:=*;cos:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|))*(g(|t_|))'".asSequent
    axs(1)._2.conclusion shouldBe "==>  (cos<<<{sin:=*;cos:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|)))'=(-sin<<<{cos:=*;sin:=._0;t_:=._1;}{{sin'=-cos,cos'=--sin,t_'=-(1)}++{sin'=cos,cos'=-sin,t_'=1}}>(t_=0&sin=0&cos=1)>>(g(|t_|)))*(g(|t_|))'".asSequent
  }

  "init" should "derive initial condition" in withMathematica { _ =>

    val exp = InterpretedSymbols.expF
    val ax = deriveInitAxiom(exp)
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

    val ax1 = deriveInitAxiom(f1)
    val ax2 = deriveInitAxiom(f2)
    val ax3 = deriveInitAxiom(f3)

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
    val dexp = getDiffAx(exp)

    dexp.isDefined shouldBe true
    dexp.get.provable.conclusion shouldBe "==>  (exp<<<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1)>>(g(|t_|)))'=exp<<<{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1)>>(g(|t_|))*(g(|t_|))'".asSequent
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

    val dfake = getDiffAx(fake)
    dfake shouldBe None
  }

  it should "derive and store init ax 1" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF
    val dexp = getInitAx(exp)

    println(dexp)
    dexp.isDefined shouldBe true
    dexp.get.provable.conclusion shouldBe "==> exp<< <{exp:=._0;t_:=._1;}{{exp'=-exp,t_'=-(1)}++{exp'=exp,t_'=1}}>(t_=0&exp=1) >>(0)=1".asSequent
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

    val dfake = getInitAx(fake)
    dfake shouldBe None
  }

  "property" should "prove exp non-negative" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    val pr = proveBy(Greater(FuncOf(exp,"f()".asTerm),Number(0)),
      propDiffUnfold("f()".asTerm, Number(0))(1) <(
        QE,
        dbx(Some(Number(1)))(1),
        dbx(Some(Number(-1)))(1)
      ))

    println(pr)
    pr shouldBe 'proved
  }

  it should "manual proof" in withMathematica { _ =>
    val exp = InterpretedSymbols.expF

    // exp(y^2) >= 1
    val pr = proveBy(GreaterEqual(FuncOf(exp,Power(Variable("y"),Number(2))),Number(1)),
      propDiffUnfold(Variable("y"), Number(0))(1) <(
        QE, //prove from initial conditions
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

    // exp(y+g(x)) > 0
    val pr = proveBy(Greater(FuncOf(exp,"y+g(x)".asTerm),Number(0)),
      propDiffUnfold("y+g(x)".asTerm, Number(0))(1) <(
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
      propDiffUnfold(Variable("x"), Number(0))(1) <(
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
      propDiffUnfold(Variable("z"), Number(0))(1) <(
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
      propDiffUnfold(Variable("x"), Number(0))(1) <(
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
      propDiffUnfold(Variable("x"), Number(0))(1) <(
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

  it should "foo" in withMathematica { _ =>
    val fml = " tanh<< <{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(t_=0&tanh=0) >>(-x) = -tanh<< <{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(t_=0&tanh=0) >>(x)".asFormula

    val pr = proveBy(fml,
      propDiffUnfold(Variable("x"), Number(0))(1) <(
        QE,
        ODE(1),
        ODE(1)
      )
    )
    println(pr)
    pr shouldBe 'proved
  }

  it should "foo2" in withMathematica { _ =>
    val fml = "tanh<< <{tanh:=._0;t_:=._1;}{{tanh'=-(1-tanh^2),t_'=-(1)}++{tanh'=1-tanh^2,t_'=1}}>(t_=0&tanh=0) >>(lambda()*x)^2 <= 1".asFormula

    val pr = proveBy(fml,
      propDiffUnfold(Variable("x"), Number(0))(1) <(
        QE,
        ODE(1),
        ODE(1)
      )
    )
    println(pr)
  }

}
