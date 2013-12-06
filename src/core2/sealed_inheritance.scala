
sealed abstract class Term

sealed class Binary (val x : Term, val y : Term) extends Term


class Plus  (x : Term, y : Term) extends Binary(x, y)
class Times (x : Term, y : Term) extends Binary(x, y)

sealed class Unary  (val x : Term) extends Term

class Neg (x : Term) extends Unary(x)

class Atom (val i : Int) extends Term

object sealed_inheritance {

  def commute(t : Term) : Term = {
    t match {
      case ret : Unary => ret
      case ret : Atom  => ret
      case ret : Plus  => new Plus(ret.x, ret.y)
/* comment me to see missing combination warning */
      case ret : Binary => ret
    }
  }

  def main(args: Array[String]) {
    var p = new Plus(new Atom(1), new Atom(2));

    println(commute(p))
  }
}
