/**
 * HyDRA API Requests
 * @author Nathan Fulton
 */
package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.api.JSONConverter
import edu.cmu.cs.ls.keymaera.core.{Sequent, Formula}

/**
 * A Request should handle all expensive computation as well as all
 * possible side-effects of a request (e.g. updating the database), but shold
 * not modify the internal state of the HyDRA server (e.g. do not update the 
 * event queue).
 * 
 * Requests objects should do work after getResultingUpdates is called, 
 * not during object construction.
 * 
 * Request.getResultingUpdates might be run from a new thread. 
 */
sealed trait Request {
  def getResultingResponses() : List[Response] //see Response.scala.
}

class CreateProblemRequest(userid : String, keyFileContents : String) extends Request {
  def getResultingResponses() = {
    try {
      //Parse the incoming file.
      val parseResult = new KeYmaeraParser().runParser(keyFileContents);
      //Create a sequent from the parse result.
      val asFormula = parseResult.asInstanceOf[Formula]
      val sequent = new Sequent(scala.collection.immutable.IndexedSeq(), 
          scala.collection.immutable.IndexedSeq(), 
          scala.collection.immutable.IndexedSeq(asFormula))
      //TODO add this proof.
      //Create a new queue. TODO this isn't actually working. ServerState needs rewriting I think.
      val newKey = ServerState.createNewKey(userid)
      
      //Return the resulting response.
      new CreateProblemResponse(sequent, newKey._1 + newKey._2) :: Nil
    }
    catch {
      case e:Exception => new ErrorResponse(e) :: Nil
    }
  }
}