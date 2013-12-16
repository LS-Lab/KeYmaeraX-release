import scala.annotation.elidable
import scala.annotation.elidable._

object TypeSafety {

  /* Typesafety in KeYmaera4 is based on sort objects to derive at
   * runtime the hierarchy of sorts that the .key file demands. Each
   * expression has a sort to which it evaluates. For example terms
   * evaluate to the sort of booleans which is represented by the type
   * BoolT and the sort object Bool. To define subsorts, we have to use
   * the class S[T] because the static type system of scala does not
   * allow us to extends the generic type T (e.g., in Subtype[T <:
   * Sort](...) extends T). All sort classes inherit from this class.
   */

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

  /* Expressions are generic in the sort type T. The notation [+T <:
   * Sort] ensures that the type T is a subtype of type Sort but also
   * that Expression[T] is a subtype of Expression[Sort]. The value
   * sort : T holds a reference to the sort object, which is used for
   * the assertions in the trait TC. For example, an expression over
   * Reals can be created by extending Expression(Real), which creates
   * a subclass of Expression[RealT].
   */

  trait TC[T <: Sort] {
    val subsort : T
    val left  : Expression[T]
    val right : Expression[T]

    applicable
    @elidable(ASSERTION) def applicable = {
      require(left.sort == right.sort && left.sort == subsort, "Sort Mismatch in Formula")
    }
  }


  class Const [T <: Sort]    (sort : T, val name : String) extends Expression(sort)
  class Equals[T <: Sort]    (val subsort : T, val left : Expression[T], val right : Expression[T]) extends Expression(Bool) with TC[T]

  /* Plus takes subtypes of S[RealT], which can be constructed by instanciating the class Subtype[T <: Sort](name : String, sort : T).
   * Hence it works for all subtypes of Real but ensures (through runtime assertions) that the left and right expression is of the same
   * subtype as real itself. This allows you to write something like v1 + v2 for velocities v1, v2 but prevents v1 + time.
   */
  class Plus  [T <: S[RealT]](val subsort : T, val left : Expression[T], val right : Expression[T]) extends Expression(subsort) with TC[T]

  def main(args : Array[String]) {

    val Time     = new Subtype("time", Real) /* subtype of real */
    val Velocity = new Subtype("velocity", Real) /* another subtype of real */

    val trueEx = new Const(Bool, "true") /* some constants */
    val oneEx  = new Const(Real, "1")
    val nowEx  = new Const(Time, "5 before 12")
    val fastEx = new Const(Velocity, "really fast")

    val laterEx = new Plus(Time, nowEx, nowEx)       /* valid because both subexpressions are over the sort Time */
    val theSameEx = new Equals(Bool, trueEx, trueEx) /* valid because both subexpressions are boolean expressions */

    /* static errors due to prevented subtyping */
//    val reallyNotTheSameEx = new Plus(Time, nowEx, trueEx) /* fails at compile time because trueEx is not a real expression */

    /* dynamic errors */
//    val notLaterEx   = new Plus(Time, nowEx, fastEx) 
      /* both parameters are of type Subtype[RealT], hence the expression cannot be disqualified at runtime.
       * The assertion fastEx.sort == Time fails and disqualifies this Expression
       */

//    val notTheSameEx = new Equals(Bool, trueEx, oneEx)
      /* Because Expression accepts common supertypes (plus notation in [+T <: Sort]), which is important
       * for generic functions over Expressions, scala cannot decide at compile time that oneEx is not of
       * a subtype RealT <: T with BoolT <: S[T] we have to discharge this type at runtime through the
       * assertion oneEx.sort == Bool.
       * Note: without this assertion scala instantiates an object of type:
       *   S[_ >: RealT with BoolT <: S[_ >: RealT with BoolT <: Sort]]
       */

//    val notSureEx    = new Plus(Time, nowEx, oneEx)
      /* Currently addition is strictly typed. That is one cannot add a subtype of real to a real without explicit cast.*/

    println("Done")
  }

}
