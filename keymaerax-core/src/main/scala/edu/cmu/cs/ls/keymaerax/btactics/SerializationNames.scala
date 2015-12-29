package edu.cmu.cs.ls.keymaerax.btactics

/**
  * Created by nfulton on 12/22/15.
  */
object SerializationNames {
  trait SerializationName {
    override def toString(): String = this match {
      case cutLName => "cutL"
      case cutRName => "cutR"
      case cutName  => "cut"
      case cutLRName => "cutLR"
    }
  }

  case object cutRName extends SerializationName
  case object cutLName extends SerializationName
  case object cutName  extends SerializationName
  case object cutLRName extends SerializationName
}
