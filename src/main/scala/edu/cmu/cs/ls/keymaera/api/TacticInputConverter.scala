package edu.cmu.cs.ls.keymaera.api

import scala.reflect.runtime.universe.TypeTag

object TacticInputConverter {

  def convert(params: Map[String,String]/*params : Map[Int,(String,String)]*/, t : List[TypeTag[_]]) = {
    var foo = params.map({case (k,v) => ""})
  }
}
