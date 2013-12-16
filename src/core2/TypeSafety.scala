import scala.annotation.elidable
import scala.annotation.elidable._

object TypeSafety {

  abstract class Sort
  abstract class S[T <: Sort] extends Sort

  class RealT extends S[RealT]
  val Real = new RealT

  class BoolT extends S[BoolT]
  val Bool = new BoolT

  class PairT[L <: Sort, R <: Sort](val left : L, val right : R) extends S[PairT[L, R]]

  class Subtype[T <: Sort](name : String, to : T) extends S[T]

  /* expressions */
  abstract class Expression[+T <: Sort](val sort : T)

  trait Binary[T <: Sort] {
    val subsort : T
    val left  : Expression[T]
    val right : Expression[T]

    applicable
    @elidable(ASSERTION) def applicable = {
      require(left.sort == right.sort && left.sort == subsort, "Sort Mismatch in Formula")
    }
  }


  class Const [T <: Sort]    (sort : T, val name : String) extends Expression(sort)
  class Equals[T <: Sort]    (val subsort : T, val left : Expression[T], val right : Expression[T]) extends Expression(Bool) with Binary[T]
  class Plus  [T <: S[RealT]](val subsort : T, val left : Expression[T], val right : Expression[T]) extends Expression(subsort) with Binary[T]

  def main(args : Array[String]) {

    val Time     = new Subtype("time", Real)
    val Velocity = new Subtype("velocity", Real)
    val trueEx = new Const(Bool, "true")
    val oneEx  = new Const(Real, "1")
    val nowEx  = new Const(Time, "5 before 12")
    val fastEx = new Const(Velocity, "really fast")

    val laterEx = new Plus(Time, nowEx, nowEx)
    val theSameEx = new Equals(Bool, trueEx, trueEx)

    /* dynamic errors */
//    val notLaterEx   = new Plus(Time, nowEx, fastEx)
//    val notSureEx    = new Plus(Time, nowEx, oneEx)
//    val notTheSameEx = new Equals(Bool, trueEx, oneEx)
    /* static errors due to prevented subtyping */
//    val reallyNotTheSameEx = new Plus(Time, nowEx, trueEx)

    println("Done")
  }

}
