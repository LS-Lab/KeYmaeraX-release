package btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.ImplicitDefinitions._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
class ImplicitDefinitionsTests extends TacticTestBase {

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

}
