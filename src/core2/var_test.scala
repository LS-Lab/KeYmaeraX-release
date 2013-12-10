object Core {

  class Sort

  object VariableCounter {
    private var next_id : Int = 0

    def next() : Int = {
      this.synchronized {
        next_id = next_id + 1;
        return next_id;
      }
    }
  }

  class Variable[+T <: Sort](val name : String, val type_object : T) {

    private val id : Int = VariableCounter.next()

    def deepName = name + "_" + id;

    def flatEquals(x : Variable[Sort]) =
      this.name == x.name && this.type_object == x.type_object

    def deepEquals(x : Variable[Sort]) =
      flatEquals(x) && this.id == x.id
  }

  def main(args : Array[String]) {
    val s = new Sort

    val v1 = new Variable("x", s)
    val v2 = new Variable("x", s)

    val v3 = new Variable("y", s)

    println(v1, v2, v1.flatEquals(v2), v1.deepEquals(v2), v1.deepName, v2.deepName, v3.deepName)
  }
}
