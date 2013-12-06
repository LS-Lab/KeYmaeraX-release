
//import java.lang.instrument._;
import org.agent._;

sealed abstract class Operator 
case class less() extends Operator
case class equals() extends Operator


class Rational 

abstract class Sort 
case class Number(r_val : Rational) extends Sort
case class Car(id : Int) extends Sort


sealed abstract class Term 
case class binaryOp (op : Operator, left : Term, right : Term) extends Term
case class atom (the : Sort) extends Term


object terms {

// term storage
  def size_of_term(x : Int) = {

    println(org.agent.InstrumentationAgent.getObjectSize(less()))

//   var obj = binaryOp(less(), atom(Car(0)), atom(Car(1)))

//   var i : Int = 0

// //  try {

//     while (i < x) {
//       obj = binaryOp(less(), obj, atom(Car(i)))
//       println(i + " " + agent.globalInst.getObjectSize(obj))
//       i = i + 1

//     }
  // } catch {
  //     case _ => println(i + " failed")
  // }
  }


// doit
//======



  def main(args: Array[String]) {
    println("huhu");
    size_of_term(1);
  }

}
