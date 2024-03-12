/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.responses.models.GetTemplatesResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, ReadRequest, Response, TemplatePOJO, UserRequest}
import edu.cmu.cs.ls.keymaerax.parser.Region

import scala.collection.immutable.{List, Nil}

class GetTemplatesRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val templates = List(
      TemplatePOJO(
        "Plain",
        "Plain dL formula",
        """ArchiveEntry "New Entry"
          |
          |Problem
          |  /* fill in dL formula here */
          |End.
          |End.""".stripMargin,
        Some(new Region(3, 2, 3, 31)),
        None,
      ),
      TemplatePOJO(
        "Structured",
        "Archive with definitions",
        """ArchiveEntry "New Entry"
          |
          |Definitions
          |  /* A constant with arbitrary value (onstrained in predicate p below) */
          |  /* Real any; */
          |
          |  /* The constant 2 */
          |  /* Real two = 2; */
          |
          |  /* An uninterpreted function of two arguments */
          |  /* Real f(Real x, Real y); */
          |
          |  /* Function x^2 */
          |  /* Real sq(Real x) = x^two; */
          |
          |  /* Predicate x<=y */
          |  /* Bool leq(Real x, Real y) <-> x<=y; */
          |
          |  /* Predicate p uses other definitions */
          |  /* Bool p(Real x) <-> any>=two & leq(x,two); */
          |
          |  /* Hybrid programs */
          |  /* HP increment ::= { x:=x+1; }; */
          |  /* HP ode ::= { {x'=sq(x) & leq(x,two) } }; */
          |  /* HP system ::= { { increment; ode; }* }; */
          |End.
          |
          |ProgramVariables
          |  /* Real x; */
          |End.
          |
          |Problem
          |  /* fill in dL formula here */
          |  /* p(x) -> [system;]leq(x,any) */
          |End.
          |
          |/* Optional tactic to prove the problem */
          |/*
          |Tactic "Proof"
          |implyR('R=="p(x)->[system{|^@|};]leq(x,any())");
          |expand "system";
          |loop("leq(x,two())", 'R=="[{increment{|^@|};ode{|^@|};}*]leq(x,any())"); <(
          |  "Init":
          |    propClose,
          |  "Post":
          |    QE,
          |  "Step":
          |    composeb('R=="[increment{|^@|};ode{|^@|};]x<=2");
          |    expandAllDefs;
          |    unfold;
          |    ODE('R=="[{x'=x^2&x<=2}]x<=2")
          |)
          |End.
          |*/
          |End.""".stripMargin,
        Some(new Region(33, 2, 33, 35)),
        None,
      ),
    )

    db.getUser(userId) match {
      case Some(_) => new GetTemplatesResponse(templates) :: Nil
      case None => new ErrorResponse("Unable to retrieve templates. Unknown user " + userId) :: Nil
    }

  }
}
