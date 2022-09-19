/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.responses.models.ListExamplesResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, ExamplePOJO, ReadRequest, Response, UserRequest}

import scala.collection.immutable.{List, Nil}

/** List of all predefined tutorials that can directly be imported from the KeYmaera X web UI, in order of display. */
class ListExamplesRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    //@todo read from the database/some web page?
    //@note Learner's mode Level=0, Industry mode Level=1
    val examples = List(
      ExamplePOJO(8, "IJCAR22",
        "Implicit Definitions Examples",
        "",
        "classpath:/examples/implicitdefinitions.kyx",
        "/examples/implicitdefinitions.png", 0),
      ExamplePOJO(6, "Textbook",
        "LFCPS 2018 Textbook Examples",
        "",
        "classpath:/keymaerax-projects/lfcps/lfcps.kyx",
        "/examples/tutorials/lfcps-examples.png", 0),
      ExamplePOJO(7, "MOD19",
        "Marktoberdorf 2019 Tutorial Examples",
        //"/keymaerax-projects/lfcps-turorial/README.md",
        "",
        "classpath:/keymaerax-projects/lfcps-tutorial/lfcps-tutorial.kyx",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(5, "POPL 2019 Tutorial",
        "Programming CPS With Proofs",
        //"/keymaerax-projects/popltutorial/README.md",
        "",
        "classpath:/keymaerax-projects/popltutorial/popltutorial.kyx",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(4, "DLDS",
        "Dynamic Logic for Dynamical Systems Marktoberdorf 2017",
        //"/keymaerax-projects/dlds/README.md",
        "",
        "classpath:/keymaerax-projects/dlds/dlds.kya",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(0, "STTT Tutorial",
        "Collection of tutorial examples",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/sttt/sttt.kyx",
        "/examples/tutorials/sttt/sttt.png", 1),
      ExamplePOJO(1, "CPSWeek 2016 Tutorial",
        "Modeling and Proving ODEs",
        "http://www.ls.cs.cmu.edu/KeYmaeraX/KeYmaeraX-tutorial.pdf",
        "classpath:/examples/tutorials/cpsweek/cpsweek.kyx",
        "/examples/tutorials/cpsweek/cpsweek.png", 1),
      ExamplePOJO(2, "FM 2016 Tutorial",
        "Tactics and Proofs",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/fm/fm.kyx",
        "/examples/tutorials/fm/fm.png", 1),
      ExamplePOJO(3, "Beginner's Tutorial",
        "Feature Tour Tutorial",
        "/dashboard.html?#/tutorials",
        "classpath:/examples/tutorials/basic/basictutorial.kyx",
        "/examples/tutorials/fm/fm.png", 0),
      //        new ExamplePOJO(3, "POPL 2019 Tutorial",
      //          "Programming CPS With Proofs",
      //          //"/keymaerax-projects/popltutorial/README.md",
      //          "",
      //          "classpath:/keymaerax-projects/popltutorial/popltutorial.kyx",
      //          "/examples/tutorials/cpsweek/cpsweek.png", 1)
    )

    db.getUser(userId) match {
      case Some(user) => new ListExamplesResponse(examples.filter(_.level <= user.level)) :: Nil
      case None => new ErrorResponse("Unable to retrieve examples. Unknown user " + userId) :: Nil
    }

  }
}