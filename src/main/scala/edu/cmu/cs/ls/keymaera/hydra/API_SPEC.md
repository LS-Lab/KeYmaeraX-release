Hydra API Specification
=======================

## /users

#### GET

Returns a list of all KeYmaera users with a registered account on this server.

 * **Parameters**: none.
 * **Data**: none.
 * **Return value**: `[ {"userid": <userid> }, ... ]`
 * **Queue addition values**: none.

#### POST /users/< newuserid >

 * **Parameters**: none.
 * **Data**: none.
 * **Return value**: `[]` or Error of on error. See JSON Formats for a definition of Error.
 * **Queue addition values**: none.
 

## /proofs/< userid >

#### GET

Returns a list of all the user's proofs.

 * **Parameters**: none.
 * **Data**: none.
 * **Return value**: `[ {"proofid": <proofid> } ]`. We might want to include more information (e.g. short names or something).
 * **Queue addition values**: none.
 * 
#### POST

Creates a new proof.

 * **Parameters**: none
 * **Data**: contents of a .key file
 * **Return value**: `{ proofid: <proofid> }`
 * **Queue addition values**: none.
 * 
#### DELETE

Deletes a user and all associated data.

 * **Parameters**: none
 * **Data**: `{"confirm": true}`. This helps prevent accidental deletion, since deletes cascade.
 * **Return value**: `[]` on success or an Error on failure. See JSON response formats (below).
 * **Queue addition values**: none.

## /proofs/< userid >/< proofid >

#### GET

Retrieves a proof. I am unsure about return vs. queue for this call.

 * **Parameters**: none.
 * **Data**: none.
 * **Return value**: A proof tree. See JSON response formats (below).
 * **Queue addition values**: none.

#### DELETE

Deletes a proof from the database.

 * **Parameters**: none.
 * **Data**: none.
 * **Return value**: `[]` on success, or an Error on failure. See JSON response formats (below).
 * **Queue addition values**: none.

## /proofs/< userid >/< proofid >/updates

#### GET

Retrieves updates from the update queue.

 * **Parameters**:
    * **currentid**: the queue index of the last retrieved update.
 * **Data**: An array of updates. See the JSON response formats (below) for a definition of updates.
 * **Return value**: `{ events: [ Events ], newCount: 12345`. See JSON Formats for a defintion of Event.
 * **Queue addition values**: none.
 * ** example**: `GET /proofs/user/5/updates?currentid=127`

#### DELETE

Prunes the update queue for this proof. Essentially manual garbage collection. This should perhaps be called if the user ever chooses to "end proving session" or "close and don't save", or something similar.

 * **Parameters**:
    * **currentid**: The event with this id in the queue -- and all preceeding events -- are deleted.
 * **Data**: none.
 * **Return value**: `[]` on success, or an Error on error (see JSON formats for a defintion of Error).
 * **Queue addition values**: none.
 * ** example**: `DELETE /proofs/user/5/updates?currentid=127`



API Tree
========

    /proofs/
    	|- <ns>							- KeYmaera proofs sorted into namespaces
    	|- user/<userid>/<proofid>/
    	    |- udpates/
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
    	|- <userid>/					- User models, can create namespaces below
    /users/								- KeYmaera users

JSON Response Formats
=====================

## JSON Format for Proof Trees

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

## JSON Format for Formulas


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

## JSON Format for Errors

    {
        "textStatus": "description of error which will be displayed to the user",
        "errorThrown": "e.g. serialization of the exception's stack trace."
    }

## JSON Format for Events

This interface defines a bare minimum; different types will have specific requirements (e.g. proof <: update). Updates are processed by the EventHandler in resources/js/EventHandler.js

Note that this is incomplete; see the recent email thread.

    {
        "type": ...,
    }

Etc.
===

### Other JSON Responses (for updates)

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

### Links with parameter templates

RFC 6570 URI Template 

Path template
http://keymaera.org/proofs{/who}						

Parameter template
http://keymaera.org/proofs/stefan/proof5/A32B{?inv}		

META
====

http://tmpvar.com/markdown.html renders this document in an easy-to-read format.
