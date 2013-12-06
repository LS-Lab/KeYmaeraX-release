object Core {

  sealed abstract class Sort

  object Bool extends Sort


  sealed abstract class Term[T <: Sort](val typeObject : T)

  type Formula = Term[Bool.type]

  case class Equals[T <: Sort](left : Term[T], right : Term[T]) extends Formula(Bool)

}
