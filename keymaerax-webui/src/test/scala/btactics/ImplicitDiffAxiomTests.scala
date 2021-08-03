package btactics

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.ImplicitDiffAxiom._
import edu.cmu.cs.ls.keymaerax.core._
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
    pr.conclusion shouldBe "==>  [{x__1'=f__1(x__1,x__2),x__2'=f__2(x__1,x__2),t_'=h_()}](x__1=g__1(t_)&x__2=g__2(t_))->[t_':=h_();]((g__1(t_))'=f__1(g__1(t_),g__2(t_))&(g__2(t_))'=f__2(g__1(t_),g__2(t_)))".asSequent
  }

  "derive diff ax" should "derive differential axiom" in withMathematica { _ =>

    val exp = Function(name="exp",domain=Real, sort=Real,
      interp = Some(/* . = exp(._0) <-> */ "<{e:=.; t :=._0;} {{e'=-(e),t'=-(1)} ++ {e'=e,t'=1}}> (t=0 & e=1)".asFormula))

    val axs = deriveDiffAxiom(List(exp))
    println(axs)

    axs.length shouldBe 1
    axs(0) shouldBe 'proved
    // parsing axs(0).conclusion shouldBe "==> (exp(g(|t_|)))'=exp(g(|t_|))*(g(|t_|))'".asSequent
  }

  it should "derive differential axiom 2" in withMathematica { _ =>

    val sin = Function(name="sin",domain=Real, sort=Real,
      interp = Some(/* . = sin(._0) <-> */ "<{c:=*; s:=.; t :=._0;} {{s'=-(c),c'=-(-s),t'=-(1)} ++ {s'=c,c'=-s,t'=1}}> (s=0 & c=1 & t=0)".asFormula))
    val cos = Function(name="cos",domain=Real, sort=Real,
      interp = Some(/* . = cos(._0) <-> */ "<{s:=*; c:=.; t :=._0;} {{s'=-(c),c'=-(-s),t'=-(1)} ++ {s'=c,c'=-s,t'=1}}> (s=0 & c=1 & t=0)".asFormula))

    val axs = deriveDiffAxiom(List(sin,cos))
    println(axs)

    axs.length shouldBe 2
    axs(0) shouldBe 'proved
    // parsing axs(0).conclusion shouldBe "==> (sin(g(|t_|)))'=cos(g(|t_|))*(g(|t_|))'".asSequent
    axs(1) shouldBe 'proved
    // parsing axs(1).conclusion shouldBe "==> (cos(g(|t_|)))'=(-sin(g(|t_|)))*(g(|t_|))'".asSequent
  }

  it should "derive differential axiom 3" in withMathematica { _ =>

    val f1 = Function(name="f1",domain=Real, sort=Real,
      interp = Some("<{b:= *; c:=*; a:=.; t :=._0;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (a=0&b=0&c=0&t=0)".asFormula))
    val f2 = Function(name="f2",domain=Real, sort=Real,
      interp = Some("<{a:= *; c:=*; b:=.; t :=._0;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (a=0&b=0&c=0&t=0)".asFormula))
    val f3 = Function(name="f3",domain=Real, sort=Real,
      interp = Some("<{b:=*; a:=*; c:=.; t :=._0;} {{a'=-(b+5),b'=-c*a,c'=-a^2,t'=-(1)} ++ {a'=b+5,b'=c*a,c'=a^2,t'=1}}> (a=0&b=0&c=0&t=0)".asFormula))

    val axs = deriveDiffAxiom(List(f1,f2,f3))
    println(axs)

    axs.length shouldBe 3
    axs(0) shouldBe 'proved
    axs(1) shouldBe 'proved
    axs(2) shouldBe 'proved

  }

}
