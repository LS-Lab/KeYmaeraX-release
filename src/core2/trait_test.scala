object Core {

  class Sort

  object Real extends Sort

  abstract class Term[T <: Sort] {
    def dump()
  }

  trait binary[L <: Sort, R <: Sort, T <: Sort] extends Term[T] {
    val left  : Term[L]
    val right : Term[L]

    def dump() {
     left.dump()
     right.dump()
    }
  }

  class fuenf extends Term[Real.type] {
    def dump() {
      println(5)
    }
  }

  class sechs extends Term[Real.type] {
    def dump() {
      println(6)
    }
  }

  class plus(val left : Term[Real.type], val right : Term[Real.type]) 
    extends Term[Real.type] with binary[Real.type, Real.type, Real.type]

  def main(args : Array[String]) {
   new plus(new fuenf, new sechs).dump()
  }
}
