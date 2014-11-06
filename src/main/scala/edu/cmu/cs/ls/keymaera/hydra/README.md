HyRDA WEB SERVER
================

HyDRA (Hybrid Distributed Reasoning Architecture) is the "middle man" between
the Javascript user interface and KeYmaera instances. HyDRA exposes a REST API
using the Spray framework.  KeYmaera instances as well as Javascript clients
interact with this API.


#API DEFINITION#

##State Update Messages (sent by KeYmaera)##

    The KeYmaera client is in edu.cmu.cs.ls.keymaera.hydra.client

    Return Format: application/json
    Return value: { success: true|false; }

    nodeClosed/<list[sequent]>
    nodePruned/<list[sequent]>
    limitExceeded/<list[sequent]>
    startingStrategy/<?>/<strategy name>

##State Query Messages (sent by GUI)##

    The JS client is in jsgui/api_client.js

    Prototypes for Event and Sequent are defined in jsgui/api_types.js

    State Request Messages:
      /startSession/
        Returns: { sessionName: <string>; }
      /getUpdates/<sessionName>
        Returns: [ Event, Event, ... ]
      /getNode/<?>
        Returns: [ Sequent, Sequent, ... ]

##Requests (sent by GUI)##

    /applyTactic/<position>/<tactic name>

##To add a new request/response

 * Add a Request class
 * Add a Update class
 * Add a path in RestApi (be sure to append to the list of routes).
 * Add a case in the HydraEventHandler javascript function.



DESIGN DISCUSSION
=================

- REST API should have multiple categories: proof, lemma, tactic
- Within proof there should be local lemmas and tactics
- Business Logic generates identifiers for proof nodes using base 36 encoding of numbers of the form 1/1/2/1/3/4 interpreted as 112134 base 5 and then translated to base 36 (digits + lowercase letters). We can do this conversion since the out-degree of proof rules is known.
- Alternatives should then be marked with specific prefix and be encoded by integers. Thus, we will have proofs/proof5/A32B/alt:3/B21 to switch to the third alternative from a specific node and then proceed along the default alternative there. This will only get big if we spawn lots and lots of alternatives in each alternative.
- If the URL ever gets too long: Introduce unique node identifiers to shorten the path
- Store all mappings in a data base on the web server side
- Give out JSON to the client such that it does not have to compute any identifiers itself
- Work on JSON instead of named objects on the client side
- Tactic applications should be of the form /proof/<nodeid>/apply?name="tacticxyz"&inv="x^2 > 5"&form="Ante,2,92B36X"
- Decouple client from background tasks with database (put tasks into database, have workers retrieve them from there)

- Spring instead of/complementing Spray? would have many libraries, excellent REST support

DATABASE SCHEMA
===============
    users
        _id
        username
        password
    
    model
        _id
        userId
        name
        date
        fileContents
        
    proof
        _id
        modelId
        name
        description
        date
        proof           - json
    



REST URI DESIGN
===============

    /proofs/
      |- <ns>							- KeYmaera proofs sorted into namespaces
      |- user/<userid>/<id>/
        |- lemmas/					- Local (and referenced?) lemmas
        |- model/					- The model, links to one of /models/...
        |- tactics/					- Local (and referenced?) tactics
        |- root/					- Proof root
          |- <nodeid>/			- Node addressing as discussed above
            |- tactics			- the applicable tactics
            |- apply			- apply a tactic (alternative: use tactic name)
            |- step				- apply the default step
            |- ante/<pos>/<n>	- a node in a formula at position pos in the antecedent
              |- tactics		
              |- apply
              |- step
            |- succ/<pos>/<n>	- a node in a formula at position pos in the succedent
              |- tactics
              |- apply
              |- step
        |- updates/<lastId> - Returns an array of new updates.
    /lemmas/
      |- <ns>/						- KeYmaera lemmas sorted into namespaces
      |- user/<userid>/				- User lemmas, can create namespaces below
    /tactics/
      |- <ns>/						- KeYmaera global tactics sorted into namespaces
      |- user/<userid>/				- User tactics, can create namespaces below
    /models/
      |- automotive/
      |- robotics/
      |- aviation/
      |- tutorials/
      |- users/<userid>      					- User models, can create namespaces below.
        |- model/<modelid>
            |- createProof          - Create a new proof (POST) (json w/ proofName, proofDescription req'd)
    /users/								- KeYmaera users

REST METHODS
============


Models
------

# /models/< userid >

Output format: schema/modelList.js

    [[name, dateAdded, modelList], ...]

Some examples for the API

Retrieve resources
------------------
GET /proofs 					- all public proofs (parameters for search options)
GET /proofs/user/<userid>		- all proofs of user <userid>
GET /proofs/user/<userid>/<id>	- proof identified by <id>

Create new resources
--------------------
POST /proofs/user/<userid>		- create a new proof for user <userid> (returns URI to new proof)
POST /users/					- create a new user

Delete resources
----------------
DELETE /proofs/<userid>/<id>	- delete proof <id>

JSON RESPONSE FORMAT
====================

HATEOAS inspired

{"id" : 5,
 "type" : "proof",
 "nodes" : [
   { "id" : "A32B",
   	 "type" : "sequent",
     "antecedent" : [  
       { "id" : 1, "formula" : "5+3<8 (imagine me as a tree)", "hidden" : true,
         "links" : [
           { "rel" : "self", "href" : "http://keymaera.org/proofs/5/A32B/1" }
         ]
       }
     ],
     ...
     "links" : [ { "rel" : "node.children", "href" : "http://keymaera.org/proofs/5/A32B/children" } ]
   }  
 ],
 "links" : [
    { "rel" : "self", "href" : "http://keymaera.org/proofs/5" },
    { "rel" : "proof.all", "href" : "http://keymaera.org/proofs" }
    { "rel" : "proof.search", "href" : "http://keymaera.org/proofs{/who,id}
 ]
}

JSON Format for Formulas
------------------------

{
  "id": 1,
  "type": "LessThan",
  "left": {
    "id": 2,
    "type": "Plus",
    "left": {
      "id": 3,
      "type": "Number",
      "str": "5"
    },
    "right": {
      "id": 4,
      "type": "Number",
      "str": "3"
    }
  },
  "right": {
    "id": 5,
    "type": "Number",
    "str": "8"
  }
}

Other JSON Responses (for updates)
---------------------------------

These are definitely necessary, since they might result from a tactic or other
user action:

{
  "id": 20,
  "type": "CreateProblem | CreateNode",
  "node": <node>
}

I'm not sure if these are necessary; although they can result from a user
action, there's probably typicallly a 1:1 between a request for the action and 
the action itself.

{
  "id": 20,
  "type": "DeleteNode",
  "nodeId": 5
}

Links with parameter templates
------------------------------
RFC 6570 URI Template 

Path template
http://keymaera.org/proofs{/who}						

Parameter template
http://keymaera.org/proofs/stefan/proof5/A32B{?inv}		


IMPLEMENTATION TECHNOLOGY
=========================

Several 

Jackson					- server-side JSON serialization
MongoDB					- database
RabittMQ				- messaging
