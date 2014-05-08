import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tools._
import java.math.BigDecimal
import java.io.File

class QETests extends FlatSpec with Matchers {
  var ml : MathematicaLink = new JLinkMathematicaLink()
  val x = Variable("x", None, Real)

  val zero = Number(new BigDecimal("0"))

  def num(n : Integer) = Number(new BigDecimal(n.toString()))
  def snum(n : String) = Number(new BigDecimal(n))

  "Quantifier Eliminator" should "verify that there exists x > 0" in {
    val f = Exists(Seq(x), GreaterThan(Real, x, zero))
    ml.qe(f) should be (True)
  }
}
