/**
 * @author Marcus Völp
 */

/**
 * Sorts
 * =====
 *
 * The rational behind the below type hierarchy Sort is to let scala
 * discarge ill typed terms whenever this is possible. That is, scala
 * will automatically check type safety for builtin sorts. However,
 * because Sorts can be user defined. We have to support the creation
 * of new Sorts, which prevents compile time checks for these sorts.
 * We therefore equipped terms over user defined sorts with runtime
 * checks to assert type safety.
 */
sealed abstract class Sort

trait Quantifiable

/**
 * Builtin sorts
 */
sealed abstract class BuiltInSort extends Sort

object Bool extends BuiltInSort with Quantifiable
object Real extends BuiltInSort with Quantifiable
object Unit extends BuiltInSort with Quantifiable

object Game    extends BuiltInSort
object Program extends BuiltInSort
object Formula extends BuiltInSort

/**
 * User defined sorts
 */
sealed class UserDefinedSort(name : String) extends Sort with Quantifiable
sealed class UserDefinedEnum(name : String, elements : list[String]) extends UserDefinedSort

/* ??? We could perhaps just create "Constant" objects for every element of an enum */

sealed class Pair[L <: Sort, R <: Sort] extends Sort
