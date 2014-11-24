package edu.cmu.cs.ls.keymaera.api

import edu.cmu.cs.ls.keymaera.core.{SuccPosition, AntePosition, Position, Formula}
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser

import scala.reflect.runtime.universe.{TypeTag,typeOf}

/**
 * Converts string input into core data structures
 * @author Stefan Mitsch
 */
object TacticInputConverter {

  /**
   * Converts string input into core data structures
   * @param params The string input
   * @param t The tag of the desired type
   * @tparam T The desired type
   * @return The string input converted to the specified type.
   */
  def convert[T](params: Map[Int,String], t: TypeTag[T]): T = {
    assert(params.size == 1)
    params.map({ case (k,v) => convert(v, t) }).head
  }

  /**
   * Converts string input into core data structures
   * @param params The string input
   * @param t The tags of the desired types
   * @tparam T The desired type of the first parameter
   * @tparam U The desired type of the second parameter
   * @return The string input converted to the specified tuple type
   */
  def convert[T,U](params: Map[Int,String], t: (TypeTag[T], TypeTag[U])): (T,U) = {
    assert(params.size == 2)
    val theParams = params.map({ case (k,v) => (k, convert(v, t.productElement(k).asInstanceOf[TypeTag[_]])) })
    (theParams.get(0).asInstanceOf[T], theParams.get(1).asInstanceOf[U])
  }

  /**
   * Converts string input into core data structures
   * @param params The string input
   * @param t The tags of the desired types
   * @tparam T The desired type of the first parameter
   * @tparam U The desired type of the second parameter
   * @tparam V The desired type of the third parameter
   * @return The string input converted to the specified tuple type
   */
  def convert[T,U,V](params: Map[Int,String], t: (TypeTag[T], TypeTag[U], TypeTag[V])): (T,U,V) = {
    assert(params.size == 3)
    val theParams = params.map({ case (k,v) => (k, convert(v, t.productElement(k).asInstanceOf[TypeTag[_]])) })
    (theParams.get(0).asInstanceOf[T], theParams.get(1).asInstanceOf[U], theParams.get(2).asInstanceOf[V])
  }

  /**
   * Converts string input into core data structures
   * @param param The string input
   * @param t The tag of the desired type
   * @tparam T The desired type
   * @return The string input converted to the specified type.
   */
  private def convert[T](param: String, t: TypeTag[T]): T = {
    if (t.tpe =:= typeOf[Option[Formula]]) new KeYmaeraParser ().parseBareExpression(param) match {
      case Some(f: Formula) => Some(f).asInstanceOf[T]
    } else if (t.tpe =:= typeOf[String]) {
      param.asInstanceOf[T]
    } else if (t.tpe =:= typeOf[Boolean]) {
      param.toBoolean.asInstanceOf[T]
    } else if (t.tpe =:= typeOf[Position]) {
      val pos = param.split(":")(1).toInt
      if (param.startsWith("ante:")) Some(new AntePosition(pos)).asInstanceOf[T]
      else Some(new SuccPosition(pos)).asInstanceOf[T]
    } else throw new IllegalArgumentException("Unknown parameter type")
  }

}
