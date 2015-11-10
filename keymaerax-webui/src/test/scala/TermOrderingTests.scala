import edu.cmu.cs.ls.keymaerax.tactics.TreeForm
import edu.cmu.cs.ls.keymaerax.tactics.TreeForm._
import org.scalatest.{Matchers, FlatSpec}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Tests for algorithms that compare terms according to different measures of complexity.
 * Created by bbohrer on 10/28/15.
 */
class TermOrderingTests extends FlatSpec with Matchers {
  def O(s: String): TermSymbol = Operator(s, None)

  val testPreference = List("+", "-", "*", "/", "^")
  val testSymbols = testPreference.map({case x => Operator(x, None)})
  val testWeighting = List((O("^"), 16), (O("/"), 8), (O("*"), 4), (O("-"), 2), (O("+"), 1))

  object TestSymbolOrdering extends Ordering[TermSymbol] {
    private def compareOps(x: String, y: String): Int = {
      testPreference.indexOf(x).compare(testPreference.indexOf(y))
    }

    def compare(sym1: TermSymbol, sym2: TermSymbol): Int = {
      (sym1, sym2) match {
        case (DiffVar(v1), DiffVar(v2)) => v1.compare(v2)
        case (Var(v1), Var(v2)) => v1.compare(v2)
        case (Func(f1), Func(f2)) => f1.compare(f2)
        case (Operator(op1, arity1), Operator(op2, arity2)) =>
          val cmp = compareOps(op1, op2)
          if (cmp != 0) cmp
          else {
            (arity1, arity2) match {
              case (None, None) => 0
              case (Some(_), None) => 1
              case (None, Some(_)) => -1
              case (Some(n1), Some(n2)) => n1.compare(n2)
            }
          }
        case (Constant(x1), Constant(x2)) => x1.value.compare(x2.value)
        case (Func(_), _) => 1
        case (_, Func(_)) => -1
        case (DiffVar(_), _) => 1
        case (_, DiffVar(_)) => -1
        case (Var(_), _) => 1
        case (_, Var(_)) => -1
        case (Operator(_, _), _) => 1
        case (_, Operator(_, _)) => -1
      }
    }
  }

  val kbTestOrdering = new KnuthBendixOrdering(testWeighting)
  val kbDepthTestOrdering = new DepthKBOrdering(testWeighting)
  val kbSizeTestOrdering = new SizeKBOrdering(testWeighting)
  val lexSymbolTestOrdering = new LexicographicSymbolOrdering(testSymbols)
  val rpoTestOrdering = new RecursivePathOrdering(TestSymbolOrdering)

  "Knuth-Bendix Ordering" should "respect weights" in {
    val t1 = "1 * 1".asTerm
    val t2 = "1 - 1".asTerm
    kbTestOrdering.compare(t1, t2) shouldBe -1
  }

  it should "ignore constants because the test weighting doesn't mention them" in {
    val t1 = "10  + 20".asTerm
    val t2 = "1 + 1".asTerm
    kbTestOrdering.compare(t1, t2) shouldBe 0
  }

  it should "let many cheap terms overpower an expensive term" in {
    val t1 = "1 * 1".asTerm
    val t2 = "(1 - 1) + (1 - 1) + (1 - 1) + (1 - 1) + (1 - 1)".asTerm
    kbTestOrdering.compare(t1, t2) shouldBe -1
  }

  it should "be transitive" in {
    val t1 = "1 - 1".asTerm
    val t2 = "1 + 1 + 1 + 1 + 1".asTerm
    kbTestOrdering.compare(t1, t2) shouldBe -1
  }

  it should "be antisymmetric" in {
    val t1 = "1 + 1 + 1 + 1 + 1".asTerm
    val t2 = "1 - 1".asTerm
    kbTestOrdering.compare(t1, t2) shouldBe 1
  }

  it should "be irreflexive" in {
    val t1 = "2 ^ 7".asTerm
    val t2 = t1
    kbTestOrdering.compare(t1, t2) shouldBe 0
  }
}
